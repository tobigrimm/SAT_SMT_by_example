#lang racket

; http://dukenukem.wikia.com/wiki/Protozoid_Slimer
;
; ***

(provide string-last-char)
(define (string-last-char s)
  (string-ref s (- (string-length s) 1))
  )

;(string-last-char "asd\r")
;(string-last-char "")

(provide dec-or-hex-string-to-number)
(define (dec-or-hex-string-to-number s)
  (if (eq? (string-last-char s) #\h)
      (string->number (string-without-last-character s) 16)
      (string->number s 10)
      )
  )

;test: (string-without-last-character "asd")
(define (string-without-last-character s)
  (substring s 0 (- (string-length s) 1))
  )

; ***

(define (string-last-char-is-newline s)
  (if (eqv? (string-length s) 0)
      #f
      (let ((last-char (string-last-char s)))
	(or 
	 (eqv? last-char #\return)
	 (eqv? last-char #\newline)
	 )
	)
      )
  )

;(string-last-char-is-newline "asd\r")
;(string-last-char-is-newline "")

; ***

(define (string-cut-last-char s)
  (substring s 0 (- (string-length s) 1))
  )

;(string-cut-last-char "asd")

; ***
; NOTE: Racket has string-trim
(define (string-trim-newlines s)
  (if (string-last-char-is-newline s) 
      (string-trim-newlines (string-cut-last-char s))
      s
      )
  )

;(string-trim-newlines "asd\r")

; ****
; file->lines in Racket?
(provide text-file-to-list)
(define (text-file-to-list filename)
  (begin
    (define file (open-input-file filename))
    (define tmp '())
    (do ((line (read-line file) (read-line file))) ((eof-object? line))
      (set! tmp (append tmp (list (string-trim-newlines line)))))
    (close-input-port file)
    tmp
    )
  )

(define (drop-first-elem-if l pred)
  (if (pred (first l))
      (drop l 1)
      l))

(define (drop-empty-lists l)
  (filter (lambda (x) (not (null? x))) l)
)

(provide split-list-into-sublists)
(define (split-list-into-sublists xs pred)
  (if (null? xs)
      '()
      (let* ((new-list (drop-first-elem-if xs pred))
            (first-chunk (takef new-list (negate pred)))
            (rest-of-list (dropf new-list (negate pred))))
        (cons first-chunk (drop-empty-lists (split-list-into-sublists rest-of-list pred))))))

(provide pick-random)
(define (pick-random lst)
  (list-ref lst (random (length lst)))
  )

; https://rosettacode.org/wiki/Population_count#Racket
(provide population-count)
(define (population-count n)
  (if (negative? n)
      (bitwise-not (population-count (bitwise-not n)))
      (let inr ((x n) (rv 0))
        (if (= x 0) rv (inr (bitwise-and x (sub1 x)) (add1 rv))))))

(provide is_2n)
(define (is_2n n)
  (= (population-count n) 1)
  )
