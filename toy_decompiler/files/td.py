# Python 2.x

import re, math, operator, random, os, subprocess, sys

show_registers_after_each_parsed_line=False # default
selftest=True
SMT_test=True
python_expr=False

RX_REGISTER="(rax|rbx|rcx|rdx|rsi|rdi)"
RX_INS="(mov|movabs|lea|mul|imul|div|idiv|not|neg|sar|sal|shr|shl|sub|add|and|or|xor)"
RX_WHITESPACE="[\t ]*"
RX_DEC="([0-9]+)"
PAT1=re.compile ("^"+RX_WHITESPACE+RX_INS+RX_WHITESPACE+RX_REGISTER+RX_WHITESPACE+"$")
PAT2=re.compile ("^"+RX_WHITESPACE+RX_INS+RX_WHITESPACE+RX_REGISTER+","+RX_WHITESPACE+"([^ ]+)"+"$")
PAT3=re.compile ("^"+RX_WHITESPACE+RX_INS+RX_WHITESPACE+RX_REGISTER+","+RX_WHITESPACE+RX_REGISTER+","+RX_WHITESPACE+"([^ ]+)"+"$")
PAT_COMMENT=re.compile("^"+RX_WHITESPACE+";.*$")
PAT_WP=re.compile ("^"+RX_WHITESPACE+"$")

map_ins_names_to_ops={ "sar" : ">>", "shr" : ">>", "sal" : "<<", "shl" : "<<", "and" : "&", "or"  : "|", "xor" : "^", "add" : "+", "sub" : "-", "mul" : "*", "imul" : "*"}

def dec_or_hex_string_to_number (s):
    if s[-1]=="h":
        return int(s[:-1], 16)
    else:
        return int(s)

def val_to_string (v):
    if v>0 and v<10000:
        return str(v)
    return "0x{0:x}".format(v)

# "accessors"
def get_expr_type(e):
    return e[0]

def get_symbol (e):
    assert get_expr_type(e)=="EXPR_SYMBOL"
    return e[1]

def get_val (e):
    assert get_expr_type(e)=="EXPR_VALUE"
    return e[1]

def is_expr_op(e):
    return get_expr_type(e)=="EXPR_OP"

def get_op (e):
    assert is_expr_op(e)
    return e[1]

def get_op1 (e):
    assert is_expr_op(e)
    return e[2]

def get_op2 (e):
    assert is_expr_op(e)
    return e[3]

def is_unary_op (op):
    return op in ["NEG", "~"]

def expr_to_string (e):
    if python_expr:
        return str(e)

    t=get_expr_type (e)
    if t=="EXPR_SYMBOL":
        return get_symbol(e)
    elif t=="EXPR_VALUE":
        return val_to_string (get_val (e))
    elif t=="EXPR_OP":
        if is_unary_op (get_op (e)):
            op_s=get_op(e)
            if op_s=="NEG":
                op_s="-"
            return "(" + op_s + expr_to_string (get_op1 (e)) + ")"
        else:
            return "(" + expr_to_string (get_op1 (e)) + " " + get_op (e) + " " + expr_to_string (get_op2 (e)) + ")"
    elif t=="EXPR_WILDCARD":
        return "EXPR_WILDCARD: "+e[1]
    elif t=="EXPR_WILDCARD_VALUE":
        return "EXPR_WILDCARD_VALUE: "+e[1]
    else:
        raise AssertionError

# "constructors"
def create_val_expr (val):
    return ("EXPR_VALUE", val)

def create_symbol_expr (val):
    return ("EXPR_SYMBOL", val)

def create_binary_expr (op, op1, op2):
    return ("EXPR_OP", op, op1, op2)

def create_unary_expr (op, op1):
    return ("EXPR_OP", op, op1)

def bind_expr (key):
    return ("EXPR_WILDCARD", key)

def bind_value (key):
    return ("EXPR_WILDCARD_VALUE", key)

def number_in_string_to_expr (s):
    val=dec_or_hex_string_to_number(s)
    if val==None:
        print "error: cannot parse number: "+s
    return create_val_expr (val)

def register_or_number_in_string_to_expr (registers, s):
    if s in registers.keys():
        return registers[s]
    else:
        return number_in_string_to_expr (s) # treat it as number

def handle_MOV (registers, op1_s, op2_s):
    registers[op1_s]=register_or_number_in_string_to_expr (registers, op2_s)

PAT_REG_PLUS_REG=re.compile ("\\["+RX_REGISTER+"\\+"+RX_REGISTER+"\\]")
PAT_REG_PLUS_VAL_PLUS_REG=re.compile ("\\["+RX_REGISTER+"\\+"+RX_DEC+"\\+"+RX_REGISTER+"\\]")

# case 1: [reg1+reg2]
# case 2: [reg1+1234+reg2]
def parse_memory (registers, s):
    parsed_case1=PAT_REG_PLUS_REG.match(s)
    if parsed_case1:
        return create_binary_expr("+", 
                register_or_number_in_string_to_expr (registers, parsed_case1.group(1)),
                register_or_number_in_string_to_expr (registers, parsed_case1.group(2)))

    parsed_case2=PAT_REG_PLUS_VAL_PLUS_REG.match(s)
    if parsed_case2:
        return create_binary_expr ("+", register_or_number_in_string_to_expr (registers, parsed_case2.group(1)),
                create_binary_expr ("+", number_in_string_to_expr (parsed_case2.group(2)),
                    register_or_number_in_string_to_expr(registers, parsed_case2.group(3))))

    print "can't parse expression: "+s
    exit(0)

# works just like handle_MOV(), but parses memory expression and makes expression from it
def handle_LEA (registers, op1_s, op2_s):
    registers[op1_s]=parse_memory (registers, op2_s)

def handle_binary_op (registers, op, op1, op2):
    op1_expr=register_or_number_in_string_to_expr (registers, op1)
    op2_expr=register_or_number_in_string_to_expr (registers, op2)
    registers[op1]=create_binary_expr (op, op1_expr, op2_expr)

def handle_unary_op (registers, op, op1):
    op1_expr=register_or_number_in_string_to_expr (registers, op1)
    registers[op1]=create_unary_expr (op, op1_expr)

def try_parse_as_binary (registers, line):
    m=PAT2.match (line)
    if m==None: # not parsed
        return False
    ins, op1, op2=m.group(1), m.group(2), m.group(3)
    if ins=="mov" or ins=="movabs":
        handle_MOV (registers, op1, op2)
    elif ins=="lea":
        handle_LEA (registers, op1, op2)
    else:
        handle_binary_op (registers, map_ins_names_to_ops[ins], op1, op2)

    return True

def handle_unary_MUL_IMUL (registers, op1):
    op1_expr=register_or_number_in_string_to_expr (registers, op1)
    result=create_binary_expr ("*", registers["rax"], op1_expr)
    registers["rax"]=result
    registers["rdx"]=create_binary_expr (">>", result, create_val_expr(64))

def handle_unary_DIV_IDIV (registers, op1):
    op1_expr=register_or_number_in_string_to_expr (registers, op1)
    current_RAX=registers["rax"]
    registers["rax"]=create_binary_expr ("/", current_RAX, op1_expr)
    registers["rdx"]=create_binary_expr ("%", current_RAX, op1_expr)

def try_parse_as_unary (registers, line):
    m=PAT1.match (line)
    if m==None: # not parsed
        return False
    ins, op1=m.group(1), m.group(2)
    if ins=="div" or ins=="idiv":
        handle_unary_DIV_IDIV(registers, op1)
    elif ins=="not":
        handle_unary_op (registers, "~", op1)
    elif ins=="neg":
        handle_unary_op (registers, "NEG", op1)
    elif ins=="mul":
        handle_unary_MUL_IMUL (registers, op1)
    else:
        print ("unhandled unary instruction: "+ins)
        exit(0)
    return True

def try_parse_as_ternary (registers, line):
    m=PAT3.match (line)
    if m==None: # not parsed
        return False
    ins, op1, op2, op3=m.group(1), m.group(2), m.group(3), m.group(4)
    if ins!="imul":
        print "only IMUL ternary operation is supported"
        exit(0)
    op2_expr=register_or_number_in_string_to_expr(registers, op2)
    op3_expr=register_or_number_in_string_to_expr(registers, op3)
    registers[op1]=create_binary_expr ("*", op2_expr, op3_expr)
    return True

def parse_asm_lines (registers, line):
    if any([try_parse_as_ternary(registers, line), 
        try_parse_as_binary(registers, line), 
        try_parse_as_unary(registers, line)]):
            if show_registers_after_each_parsed_line:
                print "line=["+line+"]"
                print "".join(map(lambda r: r+"="+expr_to_string(registers[r])+"\n", registers))
    else:
        if any([PAT_WP.match(line), PAT_COMMENT.match(line)])==False:
            print ("error! line not parsed: ["+line+"]")
            exit(0)

def reduce_step (e):
    if is_expr_op (e)==False:
        return e # expr isn't EXPR_OP, nothing to reduce (we don't reduce EXPR_SYMBOL and EXPR_VAL)

    if is_unary_op(get_op(e)):
        # recreate expr with reduced operand:
        return reducers(create_unary_expr (get_op(e), reduce_step (get_op1 (e))))
    else:
        # recreate expr with both reduced operands:
        return reducers(create_binary_expr (get_op(e), reduce_step (get_op1 (e)), reduce_step (get_op2 (e))))

def dbg_print_reduced_expr (fn, src, dst):
    print "reduction in " + fn + "() " + expr_to_string (src) + " -> " + expr_to_string (dst)
    return dst

def match_EXPR_WILDCARD (expr, pattern):
    return {pattern[1] : expr} # return {key : expr}

def match_EXPR_WILDCARD_VALUE (expr, pattern):
    if get_expr_type (expr)!="EXPR_VALUE":
        return None
    return {pattern[1] : get_val(expr)} # return {key : expr}

def is_commutative (op):
    return op in ["+", "*", "&", "|", "^"]

def match_two_ops (op1_expr, op1_pattern, op2_expr, op2_pattern):
    m1=match (op1_expr, op1_pattern)
    m2=match (op2_expr, op2_pattern)
    if m1==None or m2==None:
        return None # one of match for operands returned False, so we do the same
    # join two dicts from both operands:
    rt={}
    rt.update(m1)
    rt.update(m2)
    return rt

def match_EXPR_OP (expr, pattern):
    if get_expr_type(expr)!=get_expr_type(pattern): # be sure, both EXPR_OP.
        return None
    if get_op (expr)!=get_op (pattern): # be sure, ops type are the same.
        return None

    if (is_unary_op(get_op(expr))):
        # match unary expression.
        return match (get_op1 (expr), get_op1 (pattern))
    else:     
        # match binary expression.     

        # first try match operands as is.
        m=match_two_ops (get_op1 (expr), get_op1 (pattern), get_op2 (expr), get_op2 (pattern))
        if m!=None:
            return m
        # if matching unsuccessful, AND operation is commutative, try also swapped operands.
        if is_commutative (get_op (expr))==False:
            return None
        return match_two_ops (get_op1 (expr), get_op2 (pattern), get_op2 (expr), get_op1 (pattern))

# returns dict in case of success, or None
def match (expr, pattern):
    t=get_expr_type(pattern)
    if t=="EXPR_WILDCARD":
        return match_EXPR_WILDCARD (expr, pattern)
    elif t=="EXPR_WILDCARD_VALUE":
        return match_EXPR_WILDCARD_VALUE (expr, pattern)
    elif t=="EXPR_SYMBOL":
        if expr==pattern:
            return {}
        else:
            return None
    elif t=="EXPR_VALUE":
        if expr==pattern:
            return {}
        else:
            return None
    elif t=="EXPR_OP":
        return match_EXPR_OP (expr, pattern)
    else:
        raise AssertionError

# X+X -> X*2
# we don't use match() here (yet):
def reduce_ADD1 (expr):
    if is_expr_op(expr) and get_op (expr)=="+" and get_op1 (expr)==get_op2 (expr):
        return dbg_print_reduced_expr ("reduce_ADD1", expr, create_binary_expr ("*", get_op1 (expr), create_val_expr (2)))

    return expr # no match

# (X*A)+X -> X*(A+1)
def reduce_ADD2 (expr):
    m=match (expr, create_binary_expr ("+", create_binary_expr ("*", bind_expr ("X1"), bind_value ("A")), bind_expr ("X2")))
    if m!=None and match (m["X1"], m["X2"])!=None:
        return dbg_print_reduced_expr("reduce_ADD2", expr, create_binary_expr ("*", m["X1"], create_val_expr (m["A"]+1)))
    else:
        return expr # no match

# X & (X | ...) -> X
def reduce_AND2 (expr):
    m=match (expr, create_binary_expr ("&", create_binary_expr ("|", bind_expr ("X1"), bind_expr ("REST")), bind_expr ("X2")))
    if m!=None and match (m["X1"], m["X2"])!=None:
        return dbg_print_reduced_expr("reduce_AND2", expr, m["X1"])
    else:
        return expr # no match

# X & X -> X
def reduce_AND3 (expr):
    m=match (expr, create_binary_expr ("&", bind_expr ("X1"), bind_expr ("X2")))
    if m!=None and match (m["X1"], m["X2"])!=None:
        return dbg_print_reduced_expr("reduce_AND3", expr, m["X1"])
    else:
        return expr # no match

# X | X -> X
def reduce_OR1 (expr):
    m=match (expr, create_binary_expr ("|", bind_expr ("X1"), bind_expr ("X2")))
    if m!=None and match (m["X1"], m["X2"])!=None:
        return dbg_print_reduced_expr("reduce_OR1", expr, m["X1"])
    else:
        return expr # no match

# (~X)+1 -> -X
def reduce_ADD5 (expr):
    m=match (expr, create_binary_expr ("+", create_unary_expr ("~", bind_expr ("X")), create_val_expr (1)))
    if m!=None:
        return dbg_print_reduced_expr("reduce_ADD5", expr, create_unary_expr ("NEG", m["X"]))
    else:
        return expr # no match

# (X*n)-X -> X*(n-1)
def reduce_SUB3 (expr):
    m=match (expr, create_binary_expr ("-",
        create_binary_expr ("*", bind_expr("X1"), bind_value ("N")),
        bind_expr("X2")))
    
    if m!=None and match (m["X1"], m["X2"])!=None:
        return dbg_print_reduced_expr ("reduce_SUB3", expr, create_binary_expr ("*", m["X1"], create_val_expr (m["N"]-1)))
    else:
        return expr # no match

# ((X^Y)^Z)^Y -> X^Z
def reduce_XOR1 (expr):
    m=match(expr, create_binary_expr ("^",
        create_binary_expr("^",
            create_binary_expr ("^", bind_expr("X"), bind_expr("Y1")),
                bind_expr("Z")),
        bind_expr("Y2")))
    
    if m!=None and match (m["Y1"], m["Y2"])!=None:
        return dbg_print_reduced_expr ("reduce_XOR1", expr, create_binary_expr ("^", m["X"], m["Z"]))
    else:
        return expr # no match

# (X^Y)^Y -> X
def reduce_XOR2 (expr):
    m=match(expr, 
        create_binary_expr("^",
            create_binary_expr ("^", bind_expr("X"), bind_expr("Y1")),
                bind_expr("Y2")))
    
    if m!=None and match (m["Y1"], m["Y2"])!=None:
        return dbg_print_reduced_expr ("reduce_XOR2", expr, m["X"])
    else:
        return expr # no match

# (X^n)^m -> X^(n^m)
def reduce_XOR4 (expr):
    m=match(expr, 
        create_binary_expr("^",
            create_binary_expr ("^", bind_expr("X"), bind_value("N")),
                bind_value("M")))
    
    if m!=None:
        return dbg_print_reduced_expr ("reduce_XOR4", expr, create_binary_expr ("^", m["X"], 
            create_val_expr (m["N"]^m["M"])))
    else:
        return expr # no match

# X op 0 -> X, where op is ADD, OR, XOR, SUB
def reduce_op_0 (expr):
    # try each:
    for op in ["+", "|", "^", "-"]:
        m=match(expr, create_binary_expr(op, bind_expr("X"), create_val_expr (0)))
        if m!=None:
            return dbg_print_reduced_expr ("reduce_op_0", expr, m["X"])

    # default:
    return expr # no match

# (-X) - Y -> -(X+Y)
def reduce_SUB2 (expr):
    m=match (expr, create_binary_expr ("-", 
        create_unary_expr ("NEG", bind_expr ("X")),
        bind_expr ("Y")))
    if m==None:
        return expr # no match

    return dbg_print_reduced_expr ("reduce_SUB2", expr, create_unary_expr ("NEG", create_binary_expr ("+", m["X"], m["Y"])))

# X - (-Y) -> X+Y
def reduce_SUB5 (expr):
    m=match (expr, create_binary_expr ("-", 
        bind_expr ("X"),
        create_unary_expr ("NEG", bind_expr ("Y"))))
    if m==None:
        return expr # no match

    return dbg_print_reduced_expr ("reduce_SUB5", expr, create_binary_expr ("+", m["X"], m["Y"]))

# (X+Y)-Y -> X
# (X-Y)+Y -> X
def reduce_ADD_SUB (expr):
    # try each pair
    for x in [("+", "-"), ("-", "+")]:
        op1, op2=x[0], x[1]

        m=match (expr, create_binary_expr (op1, 
            create_binary_expr (op2, bind_expr ("X"), bind_expr("Y1")),
            bind_expr ("Y2")))

        if m!=None and match (m["Y1"], m["Y2"])!=None:
            return dbg_print_reduced_expr ("reduce_ADD_SUB", expr, m["X"])

    # now try also to reduce (Y+X)-Y -> X
    m=match (expr, create_binary_expr (op1, 
        create_binary_expr (op2, bind_expr ("Y1"), bind_expr("X")), bind_expr ("Y2")))

    if m!=None and match (m["Y1"], m["Y2"])!=None:
        return dbg_print_reduced_expr ("reduce_ADD_SUB", expr, m["X"])
    
    # default:
    return expr # no match

# (X*A)*B -> X*(A*B)
def reduce_MUL1 (expr):
    m=match (expr, create_binary_expr ("*", (create_binary_expr ("*", bind_expr ("X"), bind_value ("A"))), bind_value ("B")))
    if m==None:
        return expr # no match

    return dbg_print_reduced_expr ("reduce_MUL1", expr, create_binary_expr ("*", 
        m["X"], # new op1
        create_val_expr (m["A"] * m["B"]))) # new op2

# X<<n -> X*(2^n)
def reduce_SHL1 (expr):
    m=match (expr, create_binary_expr ("<<", bind_expr ("X"), bind_value ("Y")))
    if m==None:
        return expr # no match
    
    return dbg_print_reduced_expr ("reduce_SHL1", expr, create_binary_expr ("*", m["X"], create_val_expr (1<<m["Y"])))

# (X*n)+(X*m) -> X*(n+m)
def reduce_ADD4 (expr):
    m=match (expr, create_binary_expr ("+", 
        create_binary_expr ("*", bind_expr ("X1"), bind_value ("N")), 
        create_binary_expr ("*", bind_expr ("X2"), bind_value ("M"))))
    if m!=None and match (m["X1"], m["X2"])!=None:
        return dbg_print_reduced_expr("reduce_ADD4", expr, create_binary_expr ("*", m["X1"],
            create_val_expr (m["N"]+m["M"])))
    else:
        return expr # no match

# (X+A)+B -> X+(A+B) where A,B are values
def reduce_ADD3 (expr):
    m=match (expr, create_binary_expr ("+", 
        create_binary_expr ("+", bind_expr ("X"), bind_value ("A")),
        bind_value("B")))
    if m!=None:
        return dbg_print_reduced_expr("reduce_ADD3", expr, create_binary_expr ("+", m["X"],
            create_val_expr (m["A"]+m["B"])))
    else:
        return expr # no match

# (X-A)-B -> X-(A+B) where A,B are values
def reduce_SUB1 (expr):
    m=match (expr, create_binary_expr ("-", 
        create_binary_expr ("-", bind_expr ("X"), bind_value ("A")),
        bind_value("B")))
    if m!=None:
        return dbg_print_reduced_expr("reduce_SUB1", expr, create_binary_expr ("-", m["X"],
            create_val_expr (m["A"]+m["B"])))
    else:
        return expr # no match

# X^(-1) -> ~X
def reduce_XOR3 (expr):
    m=match (expr, create_binary_expr ("^", bind_expr ("X"), create_val_expr (0xffffffffffffffff)))
    if m==None:
        return expr # no match
    
    return dbg_print_reduced_expr ("reduce_XOR3", expr, create_unary_expr ("~", m["X"]))

# (op(op X)) -> X, where both ops are NEG or NOT
def reduce_double_NEG_or_NOT (expr):
    # try each:
    for op in ["NEG", "~"]:
        m=match (expr, create_unary_expr (op, create_unary_expr (op, bind_expr("X"))))
        if m!=None:
            return dbg_print_reduced_expr ("reduce_double_NEG_or_NOT", expr, m["X"])

    # default:
    return expr # no match

# (- (~X)) -> X+1
def reduce_NEG_NOT (expr):
    m=match (expr, create_unary_expr ("NEG", create_unary_expr ("~", bind_expr("X"))))
    if m==None:
        return expr # no match
    
    return dbg_print_reduced_expr ("reduce_NEG_NOT", expr, create_binary_expr ("+", m["X"],create_val_expr(1)))

# (~ (-X)) -> X-1
def reduce_NOT_NEG (expr):
    m=match (expr, create_unary_expr ("~", create_unary_expr ("NEG", bind_expr("X"))))
    if m==None:
        return expr # no match
    
    return dbg_print_reduced_expr ("reduce_NOT_NEG", expr, create_binary_expr ("-", m["X"],create_val_expr(1)))

# ~X | ~Y -> ~(X & Y)
def reduce_De_Morgan1 (expr):
    m=match (expr, create_binary_expr ("|",
        create_unary_expr("~", bind_expr("X")),
        create_unary_expr("~", bind_expr("Y"))))
    if m==None:
        return expr # no match
    
    return dbg_print_reduced_expr ("reduce_De_Morgan1", expr, create_unary_expr ("~", 
        create_binary_expr ("&", m["X"], m["Y"])))

# ~X & ~Y -> ~(X | Y)
def reduce_De_Morgan2 (expr):
    m=match (expr, create_binary_expr ("&",
        create_unary_expr("~", bind_expr("X")),
        create_unary_expr("~", bind_expr("Y"))))
    if m==None:
        return expr # no match
    
    return dbg_print_reduced_expr ("reduce_De_Morgan2", expr, create_unary_expr ("~", 
        create_binary_expr ("|", m["X"], m["Y"])))

# this rule must be checked before reduce_SHR2():
# (X>>n)>>m -> X>>(n+m)
def reduce_SHR1 (expr):
    m=match(expr, create_binary_expr (">>", create_binary_expr (">>", bind_expr("X"), bind_value("N")), bind_value("M")))
    if m==None:
        return expr # no match

    return dbg_print_reduced_expr ("reduce_SHR1", expr,create_binary_expr (">>", m["X"], create_val_expr (m["N"]+m["M"])))

# X>>n -> X / (2^n)
# shifting value is >64, probably generated in handle_unary_MUL_IMUL(), so postpone it
# we don't handle values >2^64 anyway
def reduce_SHR2 (expr):
    m=match(expr, create_binary_expr(">>", bind_expr("X"), bind_value("Y")))
    if m==None or m["Y"]>=64:
        return expr # no match

    return dbg_print_reduced_expr ("reduce_SHR2", expr, create_binary_expr ("/", m["X"],
        create_val_expr (1<<m["Y"])))

# FIXME: slow
# returns True if n=2^x or popcnt(n)=1
def is_2n(n):
    return bin(n).count("1")==1

# AND operation using DIV/MUL or SHL/SHR
# (X / (2^n)) * (2^n) -> X&(~((2^n)-1))
def reduce_MUL2 (expr):
    m=match(expr, create_binary_expr ("*", create_binary_expr ("/", bind_expr("X"), bind_value("N1")), bind_value("N2")))
    if m==None or m["N1"]!=m["N2"] or is_2n(m["N1"])==False: # short-circuit expression
        return expr # no match

    return dbg_print_reduced_expr("reduce_MUL2", expr, create_binary_expr ("&", m["X"],
        create_val_expr(~(m["N1"]-1)&0xffffffffffffffff)))

# n = magic number
# m = shifting coefficient
# return = 1 / (n / 2^m) = 2^m / n
def get_divisor (n, m):
    return (2**float(m))/float(n)

# (X*n)>>m, where m>=64 -> X/...
def reduce_div_by_MUL (expr):
    m=match (expr, create_binary_expr(">>", create_binary_expr ("*", bind_expr("X"), bind_value("N")), bind_value("M")))
    if m==None:
        return expr # no match
    
    divisor=get_divisor(m["N"], m["M"])
    if math.floor(divisor)==divisor:
        return dbg_print_reduced_expr ("reduce_div_by_MUL", expr, create_binary_expr ("/", m["X"], create_val_expr (int(divisor))))
    else:
        print "reduce_div_by_MUL(): postponing reduction, because divisor=", divisor
        return expr

# compose() function was copypasted from http://stackoverflow.com/a/16739439
# see also: https://en.wikipedia.org/wiki/Function_composition_(computer_science)
def compose (functions):
    def inner(arg):
        for f in reversed(functions):
            arg = f(arg)
        return arg
    return inner

# same as "return ...(reduce_MUL1 (reduce_ADD1 (reduce_ADD2 (... expr))))"
reducers=compose([
    reduce_XOR1, reduce_XOR2, reduce_XOR3, reduce_XOR4,
    reduce_op_0,
    reduce_AND2, reduce_AND3, 
    reduce_OR1, 
    reduce_MUL1, reduce_MUL2,
    reduce_ADD1, reduce_ADD2, reduce_ADD3, reduce_ADD4, reduce_ADD5,
    reduce_SUB1, reduce_SUB2, reduce_SUB3, reduce_SUB5,
    reduce_double_NEG_or_NOT,
    reduce_ADD_SUB,
    reduce_NEG_NOT,
    reduce_NOT_NEG,
    reduce_SHL1,
    reduce_SHR2, reduce_SHR1,
    reduce_div_by_MUL,
    reduce_De_Morgan1, reduce_De_Morgan2])

def reduce (e):
    print "going to reduce " + expr_to_string (e)
    new_expr=reduce_step(e)
    if new_expr==e:
        return new_expr # we are done here, expression can't be reduced further
    else:
        return reduce(new_expr) # reduced expr has been changed, so try to reduce it again

un_ops={"NEG":operator.neg,
        "~":operator.invert}

bin_ops={">>":operator.rshift,
        "<<":(lambda x, c: x<<(c&0x3f)), # operator.lshift should be here, but it doesn't handle too big counts
        "&":operator.and_,
        "|":operator.or_,
        "^":operator.xor,
        "+":operator.add,
        "-":operator.sub,
        "*":operator.mul,
        "/":operator.div,
        "%":operator.mod}

def eval_expr(e, symbols):
    t=get_expr_type (e)
    if t=="EXPR_SYMBOL":
        return symbols[get_symbol(e)]
    elif t=="EXPR_VALUE":
        return get_val (e)
    elif t=="EXPR_OP":
        if is_unary_op (get_op (e)):
            return un_ops[get_op(e)](eval_expr(get_op1(e), symbols))
        else:
            return bin_ops[get_op(e)](eval_expr(get_op1(e), symbols), eval_expr(get_op2(e), symbols))
    else:
        raise AssertionError

def do_selftest(old, new):
    for n in range(100):
        symbols={"arg1":random.getrandbits(64), 
                "arg2":random.getrandbits(64), 
                "arg3":random.getrandbits(64), 
                "arg4":random.getrandbits(64)}
        old_result=eval_expr (old, symbols)&0xffffffffffffffff # signed->unsigned
        new_result=eval_expr (new, symbols)&0xffffffffffffffff # signed->unsigned
        if old_result!=new_result:
            print "self-test failed"
            print "initial expression: "+expr_to_string(old)
            print "reduced expression: "+expr_to_string(new)
            print "initial expression result: ", old_result
            print "reduced expression result: ", new_result
            exit(0)

un_op_to_SMT_format={
        "NEG":"bvneg",
        "~":"bvnot"}

bin_op_to_SMT_format={
        "-":"bvsub",
        "+":"bvadd",
        "&":"bvand",
        "|":"bvor",
        "^":"bvxor",
        "*":"bvmul",
        "/":"bvudiv",
        "%":"bvsrem",
        "<<":"bvshl",
        ">>":"bvlshr"}

def val_to_SMT_string (v):
    return "#x%016x" % v

def expr_to_SMT_format(e):
    t=get_expr_type (e)
    if t=="EXPR_SYMBOL":
        return get_symbol(e)
    elif t=="EXPR_VALUE":
        return val_to_SMT_string (get_val (e))
    elif t=="EXPR_OP":
        if is_unary_op (get_op (e)):
            return "(" + un_op_to_SMT_format[get_op(e)] + " " + expr_to_SMT_format (get_op1 (e)) + ")"
        else:
            return "(" + bin_op_to_SMT_format[get_op(e)] + " " + expr_to_SMT_format (get_op1 (e)) + " " + expr_to_SMT_format (get_op2 (e)) + ")"

def produce_SMT_test (fname, old, new):
    f=open(fname, "w")
    f.write("(assert\n")
    f.write("\t(forall ((arg1 (_ BitVec 64)) (arg2 (_ BitVec 64)) (arg3 (_ BitVec 64)) (arg4 (_ BitVec 64)))\n")
    f.write("\t\t(=\n")
    f.write("\t\t\t"+expr_to_SMT_format(old)+"\n")
    f.write("\t\t\t"+expr_to_SMT_format(new)+"\n")
    f.write("\t\t)\n")
    f.write("\t)\n")
    f.write(")\n")
    f.write("(check-sat)\n")
    print fname+" written"

def decompile (filename):
    registers={}
  
    registers["rax"]=create_symbol_expr("initial_RAX")
    registers["rbx"]=create_symbol_expr("initial_RBX")
    registers["rdi"]=create_symbol_expr("arg1")
    registers["rsi"]=create_symbol_expr("arg2")
    registers["rdx"]=create_symbol_expr("arg3")
    registers["rcx"]=create_symbol_expr("arg4")

    filelines=[line.strip() for line in open(filename, 'r')]
    map(lambda l: parse_asm_lines (registers, l.lower()), filelines)
    expr=registers["rax"]
    reduced_expr=reduce(expr)
    if selftest:
        do_selftest(expr, reduced_expr)
    if SMT_test:
        produce_SMT_test(filename+".smt", expr, reduced_expr)
    return expr_to_string(reduced_expr)

def check (fname, mustbe):
    print "checking "+fname
    result=decompile(fname)
    if result!=mustbe:
        print "test failed for "+fname
        print "we got: "+result
        print "must be: "+mustbe
        exit(0)

def test():
    check ("tests/AND_by_shifts.s", "(arg1 & 0xfffffffffffffff8)")
    check ("tests/AND_by_shifts2.s", "(arg1 & 0xfffffffffffffff0)")
    check ("tests/AND_by_shifts3.s", "(arg1 & 0xfffffffffffffffe)")
    check ("tests/De_Morgan1.s", "(~(arg2 & arg1))")
    check ("tests/De_Morgan2.s", "(~(arg2 | arg1))")
    check ("tests/XOR1.s", "(~arg1)")
    check ("tests/XOR1_v2.s", "(~arg1)")
    check ("tests/add.s", "(arg1 + arg2)")
    check ("tests/add1.s", "(arg1 * 2)")
    check ("tests/add2.s", "(arg1 * 8)")
    check ("tests/add_by_not_neg.s", "(arg1 + 2)")
    check ("tests/add_by_sub.s", "(arg2 + arg1)")
    check ("tests/align2grain.s", "((arg1 + (arg2 - 1)) & (~(arg2 - 1)))")
    check ("tests/div_by_mult10_unsigned.s", "(arg1 / 10)")
    check ("tests/div_by_mult1234_unsigned.s", "(arg1 / 1234)")
    check ("tests/fahr_to_celsius.s", "(((arg1 - 32) * 5) / 9)")
    check ("tests/fahr_to_celsius_obf1.s", "(((arg1 - 32) * 5) / 9)")
    check ("tests/fahr_to_celsius_obf2.s", "(((arg1 - 32) * 5) / 9)")
    check ("tests/mul.s", "(arg1 * arg2)")
    check ("tests/mul19.s", "(arg1 * 19)")
    check ("tests/mul19_2.s", "(arg1 * 19)")
    check ("tests/mul19_3.s", "(arg1 * 19)")
    check ("tests/mul19_comm_test.s", "(arg1 * 19)")
    check ("tests/mul2.s", "(arg1 * 123)")
    check ("tests/mul21.s", "(arg1 * 21)")
    check ("tests/mul31_GCC.s", "(arg1 * 31)")
    check ("tests/mul_add.s", "((arg1 * arg2) + arg3)")
    check ("tests/mul_add2.s", "(arg3 + (1234 + ((arg1 * 1000) * arg2)))")
    check ("tests/mul_add3.s", "((arg1 * 1234) + (arg2 * 5678))")
    check ("tests/neg.s", "((-arg1) * arg2)")
    check ("tests/neg2.s", "(-(arg1 + arg2))")
    check ("tests/neg3.s", "(-arg1)")
    check ("tests/neg4.s", "(-arg1)")
    check ("tests/neg4_v2.s", "(-arg1)")
    check ("tests/remainder.s", "(arg1 % 3)")
    check ("tests/shift.s", "(arg1 << arg2)")
    check ("tests/sub_by_not_neg.s", "(arg1 - 2)")
    check ("tests/t10_obf.s", "arg1")
    check ("tests/t11_obf.s", "arg1")
    check ("tests/t5_obf.s", "arg1")
    check ("tests/t6_obf.s", "arg1")
    check ("tests/t7_obf.s", "(arg1 ^ 1)")
    check ("tests/t8_obf.s", "(~arg1)")
    check ("tests/t9_obf.s", "arg1")

print "toy decompiler"
print "usage:"
print "python td.py [OPTIONS] filename.s"
print "options:"
print "\t--show-registers\tshow registers after each line has been parsed"
print "\t--python-expr\t\tshow all expressions as Python expressions"
print "\t--test-all\t\trun test on all .s files"
print ""

for a in sys.argv[1:]:
    if a=="--show-registers":
        show_registers_after_each_parsed_line=True
    elif a=="--python-expr":
        python_expr=True
    elif a=="--test-all":
        test()
    else:
        print "working out "+a
        print "result="+decompile(a)

