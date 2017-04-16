#lang racket

(require "protozoid.rkt")

(define RX_REGISTER "(rax|rbx|rcx|rdx|rsi|rdi)")
(define RX_INS "(mov|movabs|lea|mul|imul|div|idiv|not|neg|sar|sal|shr|shl|sub|add|and|or|xor)")
(define RX_WHITESPACE "[\t ]*")
(define RX_DEC "([0-9]+)")
(define PAT1 (string-append "^" RX_WHITESPACE RX_INS RX_WHITESPACE RX_REGISTER RX_WHITESPACE "$"))
(define PAT2 (string-append "^" RX_WHITESPACE RX_INS RX_WHITESPACE RX_REGISTER "," RX_WHITESPACE "([^ ]+)" "$"))
(define PAT3 (string-append "^" RX_WHITESPACE RX_INS RX_WHITESPACE RX_REGISTER "," RX_WHITESPACE RX_REGISTER "," RX_WHITESPACE "([^ ]+)" "$"))
(define PAT_COMMENT (string-append "^" RX_WHITESPACE ";.*$"))
(define PAT_WP (string-append "^" RX_WHITESPACE "$"))

(define (handle_unary_DIV_IDIV registers op1)
  (let* ([op1-expr (register-or-number-in-string-to-expr registers op1)]
         [current-RAX (dict-ref registers 'R_RAX)]
         [result-to-RAX (create-binary-expr 'OP_DIV current-RAX op1-expr)]
         [result-to-RDX (create-binary-expr 'OP_REMAINDER current-RAX op1-expr)])
    (dict-set! registers 'R_RAX result-to-RAX)
    (dict-set! registers 'R_RDX result-to-RDX)))

(define (create-unary-expr op op1) (list 'EXPR_OP op op1))

(define (handle_unary_op registers op op1)
  (let ([op1-expr (register-or-number-in-string-to-expr registers op1)]
        [op1-reg (string-to-register op1)])
    (if (false? op1-reg)
        (error (string-append "can't parse register name: " op1)) ; op1 is always register, we don't support any memory
        (dict-set! registers op1-reg (create-unary-expr op op1-expr)))))

(define (try_parse_as_unary registers line)
  (let ([parsed_as_unary (regexp-match PAT1 line)])
    (if parsed_as_unary
        (let ([ins (second parsed_as_unary)] [op1 (third parsed_as_unary)])
          (cond 
            [(or (string-ci=? ins "div") (string-ci=? ins "idiv")) (handle_unary_DIV_IDIV registers op1)]
            [(string-ci=? ins "not") (handle_unary_op registers 'OP_NOT op1)]
            [(string-ci=? ins "neg") (handle_unary_op registers 'OP_NEG op1)]
            [(string-ci=? ins "mul") (handle_unary_MUL_IMUL registers op1)]
            [else (error (string-append "unhandled unary instruction: " ins))]))
        #f))) ; not parsed

(define (handle_MOV registers op1-as-string op2-as-string)
  (let ([op2-expr (register-or-number-in-string-to-expr registers op2-as-string)]
        [op1-register (string-to-register op1-as-string)])
    (my-assert (not (false? op1-register))) ; op1 is always register, we don't support any memory
    (dict-set! registers op1-register op2-expr)))

(define PAT_REG_PLUS_REG (string-append "\\[" RX_REGISTER "\\+" RX_REGISTER "\\]"))
(define PAT_REG_PLUS_VAL_PLUS_REG (string-append "\\[" RX_REGISTER "\\+" RX_DEC "\\+" RX_REGISTER "\\]"))

; case 1: [reg1+reg2]
; case 2: [reg1+1234+reg2]
(define (parse-memory registers s)
  (let ([parsed_case1 (regexp-match PAT_REG_PLUS_REG s)] [parsed_case2 (regexp-match PAT_REG_PLUS_VAL_PLUS_REG s)])
    (cond
      [parsed_case1 (create-binary-expr 'OP_ADD (register-or-number-in-string-to-expr registers (second parsed_case1)) (register-or-number-in-string-to-expr registers (third parsed_case1)))]
      [parsed_case2 (create-binary-expr 'OP_ADD
                                        (create-binary-expr 'OP_ADD (register-or-number-in-string-to-expr registers (second parsed_case2)) (number-in-string-to-expr (third parsed_case2)))
                                        (register-or-number-in-string-to-expr registers (fourth parsed_case2)))]
      [error (string-append "can't parse memory expression: " s)])))

; works just like handle_MOV, but parses memory expression and makes expression from it
(define (handle_LEA registers op1-as-string op2-as-string)
  (let ([op2-expr (parse-memory registers op2-as-string)] [op1-register (string-to-register op1-as-string)])
    (my-assert (not (false? op1-register))) ; op1 is always register, we don't support any memory
    (dict-set! registers op1-register op2-expr)))

(define (create-binary-expr op op1 op2) (list 'EXPR_OP op op1 op2))

(define (handle_binary_op registers op op1 op2)
  (let ([op1-expr (register-or-number-in-string-to-expr registers op1)]
        [op1-reg (string-to-register op1)]
        [op2-expr (register-or-number-in-string-to-expr registers op2)])
    (if (false? op1-reg)
        (error (string-append "can't parse register name: " op1))
        (dict-set! registers op1-reg (create-binary-expr op op1-expr op2-expr)))))

(define (handle_unary_MUL_IMUL registers op1)
  (let ([op1-expr (register-or-number-in-string-to-expr registers op1)] [op1-reg (string-to-register op1)])
    (if (false? op1-reg)
        (error (string-append "can't parse register name: " op1))
        (let ([result (create-binary-expr 'OP_MUL (dict-ref registers 'R_RAX) op1-expr)])
          (dict-set! registers 'R_RAX result)
          (dict-set! registers 'R_RDX (create-binary-expr 'OP_SHIFT_RIGHT result (create-val-expr 64)))))))

(define map-ins-names-to-ops
  '(("sar" . OP_SHIFT_RIGHT)
    ("shr" . OP_SHIFT_RIGHT)
    ("sal" . OP_SHIFT_LEFT)
    ("shl" . OP_SHIFT_LEFT)
    ("and" . OP_AND)
    ("or" . OP_OR)
    ("xor" . OP_XOR)
    ("add" . OP_ADD)
    ("sub" . OP_SUB)
    ("mul" . OP_MUL)
    ("imul" . OP_MUL)))

(define (try_parse_as_binary registers line)
  (let ([parsed_as_binary (regexp-match PAT2 line)])
    (if parsed_as_binary
        (let ([ins (second parsed_as_binary)] [op1 (third parsed_as_binary)] [op2 (fourth parsed_as_binary)])
          (cond
            [(or (string-ci=? ins "mov") (string-ci=? ins "movabs")) (handle_MOV registers op1 op2)]
            [(string-ci=? ins "lea") (handle_LEA registers op1 op2)]
            [else (handle_binary_op registers (dict-ref map-ins-names-to-ops (string-downcase ins)) op1 op2)]))
        #f))) ; not parsed

(define (try_parse_as_ternary registers line)
  (let ([parsed_as_ternary (regexp-match PAT3 line)])
    (if parsed_as_ternary
        (let ([ins (second parsed_as_ternary)] [op1-as-string (third parsed_as_ternary)] [op2-as-string (fourth parsed_as_ternary)] [op3-as-string (fifth parsed_as_ternary)])
          (if parsed_as_ternary
              (let ([op1-reg (string-to-register op1-as-string)] [op2-expr (register-or-number-in-string-to-expr registers op2-as-string)] [op3-expr (register-or-number-in-string-to-expr registers op3-as-string)])
                (dict-set! registers op1-reg (create-binary-expr 'OP_MUL op2-expr op3-expr)))
              (error "only IMUL ternary operation is supported")))
        #f))) ; not parsed

; try each function. stop if any of them returned #t
(define (parse-asm-line registers line)
  (or
   (try_parse_as_ternary registers line)
   (try_parse_as_binary registers line)
   (try_parse_as_unary registers line)
   (regexp-match PAT_COMMENT line)
   (regexp-match PAT_WP line)
   (error (string-append "error! line not parsed: " line))))

(define (create-symbol s) (list 'EXPR_SYMBOL s))

(define (create-val-expr val) (list 'EXPR_VALUE val))

(define register-names-table '(("rax" . R_RAX) ("rbx" . R_RBX) ("rcx" . R_RCX) ("rdx" . R_RDX) ("rsi" . R_RSI) ("rdi" . R_RDI)))

(define (string-to-register op)
  (if (dict-has-key? register-names-table op)
      (dict-ref register-names-table (string-downcase op))
      #f)) ; can't find register name in table

;test: (number-in-string-to-expr "123")
;test: (number-in-string-to-expr "29ah")
(define (number-in-string-to-expr s)
  (let ([val (dec-or-hex-string-to-number s)])
    (if val
        (create-val-expr val)
        (error (string-append "error: cannot parse number: " s)))))

(define (register-or-number-in-string-to-expr registers s)
  (let ([register (string-to-register s)])
    (if (false? register) (number-in-string-to-expr s) (dict-ref registers register))))

(define (commutative? op) (member op (list 'OP_ADD 'OP_MUL 'OP_AND 'OP_OR 'OP_XOR)))

(define (op-to-string op)
  (dict-ref '((OP_SHIFT_LEFT . "<<")
              (OP_SHIFT_RIGHT . ">>")
              (OP_SUB . "-")
              (OP_ADD . "+")
              (OP_MUL . "*")
              (OP_DIV . "/")
              (OP_NOT . "~")
              (OP_NEG . "-")
              (OP_AND . "&")
              (OP_OR . "|")
              (OP_XOR . "^")
              (OP_REMAINDER . "%")) op))

(define (unary-op? op) (member op (list 'OP_NEG 'OP_NOT)))

(define (val->string v)
  (if (and (> v 0) (< v 10000))
      (number->string v)
      (string-append "0x" (number->string v 16))))

(define (expr->string e)
  (case (get-expr-type e)
    ['EXPR_SYMBOL (get-symbol e)]
    ['EXPR_VALUE (val->string (get-val e))]
    ['EXPR_OP
     (if (unary-op? (get-op e))
         (string-append "(" (op-to-string (get-op e)) (expr->string (get-op1 e)) ")")
         (string-append "(" (expr->string (get-op1 e)) " " (op-to-string (get-op e)) " " (expr->string (get-op2 e)) ")"))]
    [else (error "error")]))

(define (match-two-ops op1-expr op1-pattern op2-expr op2-pattern)
  (let ([m1 (match op1-expr op1-pattern)] [m2 (match op2-expr op2-pattern)])
    (if (or (false? m1) (false? m2))
        #f ; one of match for operands returned #f, so we do the same
        (append m1 m2)))) ; join two a-lists from both operands

(define (match_EXPR_WILDCARD expr pattern)
  (list (cons (second pattern) expr))) ; return (key . expr)

(define (match_EXPR_WILDCARD_VALUE expr pattern)
  (if (eq? (get-expr-type expr) 'EXPR_VALUE) (list (cons (second pattern) (get-val expr))) #f)) ; return (key . expr)

(define (match_EXPR_OP expr pattern)
  (and
   (eq? (get-expr-type expr) (get-expr-type pattern)) ; be sure, both EXPR_OP.
   (eq? (get-op expr) (get-op pattern)) ; be sure, ops type are the same.
                                         
   (if (unary-op? (get-op expr))
       ; match unary expression.
       (match (get-op1 expr) (get-op1 pattern))
       
       ; match binary expression.     
       ; first try match operands as is.
       ; if matching unsuccessful, AND operation is commutative, try also swapped operands.
       ; first OR is used here as short-circuit.
       (or (match-two-ops (get-op1 expr) (get-op1 pattern) (get-op2 expr) (get-op2 pattern))
           (and (commutative? (get-op expr)) (match-two-ops (get-op1 expr) (get-op2 pattern) (get-op2 expr) (get-op1 pattern)))))))

; returns joined a-list in case of success, or #f
(define (match expr pattern)
  (case (get-expr-type pattern)
    ['EXPR_WILDCARD (match_EXPR_WILDCARD expr pattern)]
    ['EXPR_WILDCARD_VALUE (match_EXPR_WILDCARD_VALUE expr pattern)]
    ['EXPR_SYMBOL (if (equal? expr pattern) '() #f)]
    ['EXPR_VALUE (if (equal? expr pattern) '() #f)]
    ['EXPR_OP (match_EXPR_OP expr pattern)]
    [else error]))

(define (get-expr-type expr) (first expr))

(define (my-assert expr) (unless expr error))

(define (get-op expr) (my-assert (expr-op? expr)) (second expr))

(define (get-op1 expr) (my-assert (expr-op? expr)) (third expr))

(define (get-op2 expr) (my-assert (expr-op? expr)) (fourth expr))

(define (get-val expr) (my-assert (eq? (get-expr-type expr) 'EXPR_VALUE)) (second expr))

(define (get-symbol expr) (my-assert (eq? (get-expr-type expr) 'EXPR_SYMBOL)) (second expr))

(define (bind-expr key) (list 'EXPR_WILDCARD key))

(define (bind-value key) (list 'EXPR_WILDCARD_VALUE key))

; return dst, so a call to this function can be chained:
(define (dbg-print-reduced-expr fn src dst)
  (display (string-append "reduction in " fn "() " (expr->string src) " -> " (expr->string dst) "\n"))
  dst)

; (X*A)*B -> X*(A*B)
(define (reduce_MUL1 expr)
  (let ([m (match expr (create-binary-expr 'OP_MUL (create-binary-expr 'OP_MUL (bind-expr 'X) (bind-value 'A)) (bind-value 'B)))])
    (if m
        (dbg-print-reduced-expr "reduce_MUL1" expr (create-binary-expr 'OP_MUL
                                                                       (dict-ref m 'X) ; new op1
                                                                       (create-val-expr (* (dict-ref m 'A) (dict-ref m 'B))))) ; new op2
        expr))) ; no match

(define (expr-op? expr) (eq? (get-expr-type expr) 'EXPR_OP))

(define (ops-equal? expr) (my-assert (expr-op? expr)) (equal? (get-op1 expr) (get-op2 expr)))

; X+X -> X*2
; we don't use match() here
(define (reduce_ADD1 expr)
  (if (and (expr-op? expr) (eq? (get-op expr) 'OP_ADD) (ops-equal? expr))
      (dbg-print-reduced-expr "reduce_ADD1" expr (create-binary-expr 'OP_MUL (get-op1 expr) (create-val-expr 2)))
      expr)) ; no match

; (X*A)+X -> X*(A+1)
(define (reduce_ADD2 expr)
  (let ([m (match expr (create-binary-expr 'OP_ADD (create-binary-expr 'OP_MUL (bind-expr 'X1) (bind-value 'A)) (bind-expr 'X2)))])
    (if (and m (match (dict-ref m 'X1) (dict-ref m 'X2)))
        (dbg-print-reduced-expr "reduce_ADD2" expr (create-binary-expr 'OP_MUL (dict-ref m 'X1) (create-val-expr (+ (dict-ref m 'A) 1))))
        expr))) ; no match

; (X+A)+B -> X+(A+B) where A,B are values
(define (reduce_ADD3 expr)
  (let ([m (match expr (create-binary-expr 'OP_ADD (create-binary-expr 'OP_ADD (bind-expr 'X) (bind-value 'A)) (bind-value 'B)))])
    (if m
        (dbg-print-reduced-expr "reduce_ADD3" expr (create-binary-expr 'OP_ADD (dict-ref m 'X) (create-val-expr (+ (dict-ref m 'A) (dict-ref m 'B)))))
        expr))) ; no match

; (X*n)+(X*m) -> X*(n+m)
(define (reduce_ADD4 expr)
  (let ([m (match expr (create-binary-expr 'OP_ADD
                                           (create-binary-expr 'OP_MUL (bind-expr 'X1) (bind-value 'N))
                                           (create-binary-expr 'OP_MUL (bind-expr 'X2) (bind-value 'M))))])
    (if (and m (match (dict-ref m 'X1) (dict-ref m 'X2)))
        (dbg-print-reduced-expr "reduce_ADD4" expr (create-binary-expr 'OP_MUL (dict-ref m 'X1) (create-val-expr (+ (dict-ref m 'N) (dict-ref m 'M)))))
        expr))) ; no match

; (~X)+1 -> -X
(define (reduce_ADD5 expr)
  (let ([m (match expr (create-binary-expr 'OP_ADD
                                           (create-unary-expr 'OP_NOT (bind-expr 'X))
                                           (create-val-expr 1)))])
    (if m
        (dbg-print-reduced-expr "reduce_ADD5" expr (create-unary-expr 'OP_NEG (dict-ref m 'X)))
        expr))) ; no match

; (X-A)-B -> X-(A+B) where A,B are values
(define (reduce_SUB1 expr)
  (let ([m (match expr (create-binary-expr 'OP_SUB (create-binary-expr 'OP_SUB (bind-expr 'X) (bind-value 'A)) (bind-value 'B)))])
    (if m
        (dbg-print-reduced-expr "reduce_SUB1" expr (create-binary-expr 'OP_SUB (dict-ref m 'X) (create-val-expr (+ (dict-ref m 'A) (dict-ref m 'B)))))
        expr))) ; no match

; (-X) - Y -> X+Y
(define (reduce_SUB2 expr)
  (let ([m (match expr (create-binary-expr 'OP_SUB (create-unary-expr 'OP_NEG (bind-expr 'X)) (bind-expr 'Y)))])
    (if m
        (dbg-print-reduced-expr "reduce_SUB2" expr (create-binary-expr 'OP_ADD (dict-ref m 'X) (dict-ref m 'Y)))
        expr))) ; no match

; (X*n)-X -> X*(n-1)
(define (reduce_SUB3 expr)
  (let ([m (match expr (create-binary-expr 'OP_SUB (create-binary-expr 'OP_MUL (bind-expr 'X1) (bind-value 'N)) (bind-expr 'X2)))])
    (if (and m (match (dict-ref m 'X1) (dict-ref m 'X2)))
        (dbg-print-reduced-expr "reduce_SUB3" expr (create-binary-expr 'OP_MUL (dict-ref m 'X1) (create-val-expr (- (dict-ref m 'N) 1))))
        expr))) ; no match

; (X - Y) - X -> Y
(define (reduce_SUB4 expr)
  (let ([m (match expr (create-binary-expr 'OP_SUB (create-binary-expr 'OP_SUB (bind-expr 'X1) (bind-expr 'Y)) (bind-expr 'X2)))])
    (if (and m (match (dict-ref m 'X1) (dict-ref m 'X2)))
        (dbg-print-reduced-expr "reduce_SUB4" expr (create-unary-expr 'OP_NEG (dict-ref m 'Y)))
        expr))) ; no match

; (~ (-X)) -> X-1
(define (reduce_NOT_NEG expr)
  (let ([m (match expr (create-unary-expr 'OP_NOT (create-unary-expr 'OP_NEG (bind-expr 'X))))])
    (if m
        (dbg-print-reduced-expr "reduce_NOT_NEG" expr (create-binary-expr 'OP_SUB (dict-ref m 'X) (create-val-expr 1)))
        expr))) ; no match

; (- (~X)) -> X+1
(define (reduce_NEG_NOT expr)
  (let ([m (match expr (create-unary-expr 'OP_NEG (create-unary-expr 'OP_NOT (bind-expr 'X))))])
    (if m
        (dbg-print-reduced-expr "reduce_NEG_NOT" expr (create-binary-expr 'OP_ADD (dict-ref m 'X) (create-val-expr 1)))
        expr))) ; no match

; (-(-X)) -> X
(define (reduce_NEG_NEG expr)
  (let ([m (match expr (create-unary-expr 'OP_NEG (create-unary-expr 'OP_NEG (bind-expr 'X))))])
    (if m
        (dbg-print-reduced-expr "reduce_NEG_NEG" expr (dict-ref m 'X))
        expr))) ; no match

; ((X^Y)^Z)^Y -> X^Z
(define (reduce_XOR1 expr)
  (let ([m (match expr
             (create-binary-expr 'OP_XOR
                                 (create-binary-expr 'OP_XOR
                                                     (create-binary-expr 'OP_XOR (bind-expr 'X) (bind-expr 'Y1)) (bind-expr 'Z))
                                 (bind-expr 'Y2)))])
    (if (and m (match (dict-ref m 'Y1) (dict-ref m 'Y2)))
        (dbg-print-reduced-expr "reduce_XOR1" expr (create-binary-expr 'OP_XOR (dict-ref m 'X) (dict-ref m 'Z)))
        expr))) ; no match

; (X^Y)^Y -> X
(define (reduce_XOR2 expr)
  (let ([m (match expr
             (create-binary-expr 'OP_XOR
                                 (create-binary-expr 'OP_XOR (bind-expr 'X) (bind-expr 'Y1))
                                 (bind-expr 'Y2)))])
    (if (and m (match (dict-ref m 'Y1) (dict-ref m 'Y2)))
        (dbg-print-reduced-expr "reduce_XOR2" expr (dict-ref m 'X))
        expr))) ; no match

; X^(-1) -> ~X
(define (reduce_XOR3 expr)
  (let ([m (match expr
             (create-binary-expr 'OP_XOR (bind-expr 'X) (create-val-expr #xffffffffffffffff)))])
    (if m
        (dbg-print-reduced-expr "reduce_XOR3" expr (create-unary-expr 'OP_NOT (dict-ref m 'X)))
        expr))) ; no match

; (X^n)^m -> X^(n^m)
(define (reduce_XOR4 expr)
  (let ([m (match expr
             (create-binary-expr 'OP_XOR (create-binary-expr 'OP_XOR (bind-expr 'X) (bind-value 'N)) (bind-value 'M)))])
    (if m
        (dbg-print-reduced-expr "reduce_XOR4" expr (create-binary-expr 'OP_XOR (dict-ref m 'X) (create-val-expr (bitwise-xor (dict-ref m 'M) (dict-ref m 'N)))))
        expr))) ; no match

; X^0 -> X
(define (reduce_XOR5 expr)
  (let ([m (match expr
             (create-binary-expr 'OP_XOR (bind-expr 'X) (create-val-expr 0)))])
    (if m
        (dbg-print-reduced-expr "reduce_XOR5" expr (dict-ref m 'X))
        expr))) ; no match

; X & X -> X
(define (reduce_AND1 expr)
  (let ([m (match expr
             (create-binary-expr 'OP_AND (bind-expr 'X1) (bind-expr 'X2)))])
    (if (and m (match (dict-ref m 'X1) (dict-ref m 'X2)))
        (dbg-print-reduced-expr "reduce_AND1" expr (dict-ref m 'X1))
        expr))) ; no match

; X & (X | ...) -> X
(define (reduce_AND2 expr)
  (let ([m (match expr
             (create-binary-expr 'OP_AND (bind-expr 'X1) (create-binary-expr 'OP_OR (bind-expr 'X2) (bind-expr 'REST))))])
    (if (and m (match (dict-ref m 'X1) (dict-ref m 'X2)))
        (dbg-print-reduced-expr "reduce_AND2" expr (dict-ref m 'X1))
        expr))) ; no match

; X | X -> X
(define (reduce_OR1 expr)
  (let ([m (match expr
             (create-binary-expr 'OP_OR (bind-expr 'X1) (bind-expr 'X2)))])
    (if (and m (match (dict-ref m 'X1) (dict-ref m 'X2)))
        (dbg-print-reduced-expr "reduce_OR1" expr (dict-ref m 'X1))
        expr))) ; no match

; X<<n -> X*(2^n)
(define (reduce_SHL1 expr)
  (let ([m (match expr
             (create-binary-expr 'OP_SHIFT_LEFT (bind-expr 'X) (bind-value 'Y)))])
    (if m
        (dbg-print-reduced-expr "reduce_SHL1" expr (create-binary-expr 'OP_MUL (dict-ref m 'X) (create-val-expr (arithmetic-shift 1 (dict-ref m 'Y)))))
        expr))) ; no match

; this rule must be checked before reduce_SHR2:
; (X>>n)>>m -> X>>(n+m)
(define (reduce_SHR1 expr)
  (let ([m (match expr
             (create-binary-expr 'OP_SHIFT_RIGHT
                                 (create-binary-expr 'OP_SHIFT_RIGHT (bind-expr 'X) (bind-value 'N))
                                 (bind-value 'M)))])
    (if m
        (dbg-print-reduced-expr "reduce_SHR1" expr (create-binary-expr 'OP_SHIFT_RIGHT (dict-ref m 'X) (create-val-expr (+ (dict-ref m 'N) (dict-ref m 'M)))))
        expr))) ; no match

; X>>n -> X / (2^n)
; shifting value is >64, probably generated in handle_unary_MUL_IMUL(), so postpone it
; we don't handle values >2^64 anyway
(define (reduce_SHR2 expr)
  (let ([m (match expr
             (create-binary-expr 'OP_SHIFT_RIGHT (bind-expr 'X) (bind-value 'Y)))])
    (if (and m (< (dict-ref m 'Y) 64))
        (dbg-print-reduced-expr "reduce_SHR2" expr (create-binary-expr 'OP_DIV (dict-ref m 'X) (create-val-expr (arithmetic-shift 1 (dict-ref m 'Y)))))
        expr))) ; no match

; AND operation using DIV/MUL or SHL/SHR
; (X / (2^n)) * (2^n) -> X&(~((2^n)-1))
(define (reduce_MUL2 expr)
  (let ([m (match expr
             (create-binary-expr 'OP_MUL (create-binary-expr 'OP_DIV (bind-expr 'X) (bind-value 'N1)) (bind-value 'N2)))])
    (if (and m (= (dict-ref m 'N1) (dict-ref m 'N2)) (is_2n (dict-ref m 'N1)))
        (dbg-print-reduced-expr "reduce_MUL2" expr (create-binary-expr 'OP_AND (dict-ref m 'X)
                                                                       (create-val-expr (bitwise-and (bitwise-not(- (dict-ref m 'N1) 1)) #xffffffffffffffff))))
        expr))) ; no match

; ~X | ~Y -> ~(X & Y)
(define (reduce_De_Morgan1 expr)
  (let ([m (match expr
             (create-binary-expr 'OP_OR
                                 (create-unary-expr 'OP_NOT (bind-expr 'X))
                                 (create-unary-expr 'OP_NOT (bind-expr 'Y))))])
    (if m
        (dbg-print-reduced-expr "reduce_De_Morgan1" expr (create-unary-expr 'OP_NOT (create-binary-expr 'OP_AND (dict-ref m 'X) (dict-ref m 'Y))))
        expr))) ; no match

; ~X & ~Y -> ~(X | Y)
(define (reduce_De_Morgan2 expr)
  (let ([m (match expr
             (create-binary-expr 'OP_AND
                                 (create-unary-expr 'OP_NOT (bind-expr 'X))
                                 (create-unary-expr 'OP_NOT (bind-expr 'Y))))])
    (if m
        (dbg-print-reduced-expr "reduce_De_Morgan2" expr (create-unary-expr 'OP_NOT (create-binary-expr 'OP_OR (dict-ref m 'X) (dict-ref m 'Y))))
        expr))) ; no match

; n = magic number
; m = shifting coefficient
; return = 1 / (n / 2^m) = 2^m / n
(define (get-divisor n m) (/ (expt 2 m) n))

; (X*n)>>m, where m>=64 -> X/...
(define (reduce_div_by_MUL expr)
  (let ([m (match expr
             (create-binary-expr 'OP_SHIFT_RIGHT (create-binary-expr 'OP_MUL (bind-expr 'X) (bind-value 'N)) (bind-value 'M)))])
    (if m
        (let ([divisor (exact->inexact (get-divisor (dict-ref m 'N) (dict-ref m 'M)))])
          (if (integer? divisor)
              (dbg-print-reduced-expr "reduce_div_by_MUL" expr (create-binary-expr 'OP_DIV (dict-ref m 'X) (create-val-expr (inexact->exact divisor))))
              (begin
                (display (string-append "reduce_div_by_MUL(): postponing reduction, because divisor=" (number->string divisor) "\n"))
                expr))) ; no match
        expr))) ; no match

(define (reducers expr)
  ((compose reduce_De_Morgan1 reduce_De_Morgan2
            reduce_AND1 reduce_AND2
            reduce_OR1
            reduce_SHL1
            reduce_SHR2 reduce_SHR1
            reduce_XOR1 reduce_XOR2 reduce_XOR3 reduce_XOR4 reduce_XOR5
            reduce_MUL1 reduce_MUL2
            reduce_NOT_NEG
            reduce_NEG_NOT
            reduce_NEG_NEG
            reduce_SUB1 reduce_SUB2 reduce_SUB3 reduce_SUB4
            reduce_ADD1 reduce_ADD2 reduce_ADD3 reduce_ADD4 reduce_ADD5
            reduce_div_by_MUL) expr))

(define (reduce_step e)
  (if (expr-op? e)
      (reducers
       (if (unary-op? (get-op e))
           (create-unary-expr (get-op e) (reduce_step (get-op1 e))) ; recreate expr with reduced operand
           (create-binary-expr (get-op e) (reduce_step (get-op1 e)) (reduce_step (get-op2 e))))) ; recreate expr with reduced operands
      e)) ; expr isn't EXPR_OP, nothing to reduce (we don't reduce EXPR_SYMBOL and EXPR_VAL)

(define (reduce e)
  (display (string-append "going to reduce " (expr->string e) "\n"))
  (let ([new_expr (reduce_step e)])
    (if (equal? e new_expr)
        new_expr
        (reduce_step new_expr)))) ; reduced expr is not the same, so try to reduce it again

(define (decompile filename)
  (define registers (make-hash))
  
  (dict-set! registers 'R_RAX (create-symbol "initial_RAX"))
  (dict-set! registers 'R_RBX (create-symbol "initial_RBX"))
  (dict-set! registers 'R_RDI (create-symbol "arg1"))
  (dict-set! registers 'R_RSI (create-symbol "arg2"))
  (dict-set! registers 'R_RDX (create-symbol "arg3"))
  (dict-set! registers 'R_RCX (create-symbol "arg4"))
  
  (map (lambda (l) (parse-asm-line registers l)) (file->lines filename))
  (expr->string (reduce (dict-ref registers 'R_RAX))))

(define (check result mustbe)
  (if (equal? result mustbe)
      #t ; OK
      (error (string-append "check() failed. result=" result " mustbe=" mustbe))))

(define tests
  '(("AND_by_shifts.s" . "(arg1 & 0xfffffffffffffff8)")
    ("AND_by_shifts2.s" . "(arg1 & 0xfffffffffffffff0)")
    ("AND_by_shifts3.s" . "(arg1 & 0xfffffffffffffffe)")
    ("De_Morgan1.s" . "(~(arg2 & arg1))")
    ("De_Morgan2.s" . "(~(arg2 | arg1))")
    ("XOR1.s" . "(~arg1)")
    ("XOR1_v2.s" . "(~arg1)")
    ("add.s" . "(arg1 + arg2)"))
    ("add1.s" . "(arg1 * 2)")
    ("add2.s" . "(arg1 * 8)")
    ("add_by_not_neg.s" . "(arg1 + 2)")
    ("add_by_sub.s" . "(arg1 + arg2)")
    ("align2grain.s" . "((arg1 + (arg2 - 1)) & (~(arg2 - 1)))")
    ("div_by_mult10_unsigned.s" . "(arg1 / 10)")
    ("div_by_mult1234_unsigned.s" . "(arg1 / 1234)")
    ("fahr_to_celsius.s" . "(((arg1 - 32) * 5) / 9)")
    ("mul.s" . "(arg1 * arg2)")
    ("mul19.s" . "(arg1 * 19)")
    ("mul19_2.s" . "(arg1 * 19)")
    ("mul19_3.s" . "(arg1 * 19)")
    ("mul19_comm_test.s" . "(arg1 * 19)")
    ("mul2.s" . "(arg1 * 123)")
    ("mul21.s" . "(arg1 * 21)")
    ("mul_add.s" . "((arg1 * arg2) + arg3)")
    ("mul_add2.s" . "((arg3 + 1234) + ((arg1 * 1000) * arg2))")
    ("mul_add3.s" . "((arg1 * 1234) + (arg2 * 5678))")
    ("neg.s" . "((-arg1) * arg2)")
    ("neg2.s" . "(-(arg1 + arg2))")
    ("neg3.s" . "(-arg1)")
    ("neg4.s" . "(-arg1)")
    ("neg4_v2.s" . "(-arg1)")
    ("remainder.s" . "(arg1 % 3)")
    ("shift.s" . "(arg1 << arg2)")
    ("sub_by_not_neg.s" . "(arg1 - 2)")
    ("t10_obf.s" . "arg1")
    ("t11_obf.s" . "arg1")
    ("t5_obf.s" . "arg1")
    ("t6_obf.s" . "arg1")
    ("t7_obf.s" . "(arg1 ^ 1)")
    ("t8_obf.s" . "(~arg1)")
    ("t9_obf.s" . "arg1"))

(define (test)
  (for/list ([(filename mustbe) (in-dict tests)])
    (check (decompile (string-append "tests/" filename)) mustbe)))

(test)
