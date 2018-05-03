#!/usr/bin/env python
from z3 import *
import sys

I_AND, I_OR, I_XOR, I_NOT, I_NOR3 = 0,1,2,3,4

# 1-bit NOT
"""
INPUTS=[0b10]
OUTPUTS=[0b01]
BITS=2
add_always_false=False
add_always_true=True
avail=[I_XOR]
#avail=[I_NOR3]
"""

# 2-input AND
"""
INPUTS=[0b1100, 0b1010]
OUTPUTS=[0b1000]
BITS=4
add_always_false=False
add_always_true=False
avail=[I_OR, I_NOT]
#avail=[I_NOR3]
"""

# 2-input XOR
#"""
INPUTS=[0b1100, 0b1010]
OUTPUTS=[0b0110]
BITS=4
add_always_false=False
#add_always_false=True
add_always_true=False
#add_always_true=True
#avail=[I_NOR3]
#avail=[I_AND, I_NOT]
avail=[I_OR, I_NOT]
#"""

# parity (or popcnt1)
""" TT for parity
000 0
001 1
010 1
011 0
100 1
101 0
110 0
111 0
"""
"""
INPUTS=[0b11110000, 0b11001100, 0b10101010]
OUTPUTS=[0b00010110]
BITS=8
add_always_false=False
add_always_true=False
#add_always_false=True
#add_always_true=True
avail=[I_AND, I_XOR, I_OR, I_NOT]
#avail=[I_XOR, I_OR, I_NOT]
#avail=[I_AND, I_OR, I_NOT]
"""
    
# full-adder
"""
INPUTS=[0b11110000, 0b11001100, 0b10101010]
OUTPUTS=[0b11101000, 0b10010110] # carry-out, sum
BITS=8
add_always_false=False
add_always_true=False
avail=[I_AND, I_OR, I_XOR, I_NOT]
#avail=[I_AND, I_OR, I_NOT]
#avail=[I_NOR3]
"""

# popcnt
""" TT for popcnt

in  HL
000 00
001 01
010 01
011 10
100 01
101 10
110 10
111 11
"""
"""
INPUTS=[0b11110000, 0b11001100, 0b10101010]
OUTPUTS=[0b11101000, 0b10010110] # high, low
BITS=8
add_always_false=False
add_always_true=False
#avail=[I_AND, I_OR, I_XOR, I_NOT]
avail=[I_NOR3]
"""

# majority for 3 bits
""" TT for majority (true if 2 or 3 bits are True)
000 0
001 0
010 0
011 1
100 0
101 1
110 1
111 1
"""
"""
INPUTS=[0b11110000, 0b11001100, 0b10101010]
OUTPUTS=[0b11101000]
BITS=8
add_always_false=False
add_always_true=False
avail=[I_AND, I_OR, I_XOR, I_NOT]
"""

# 2-bit adder:
"""
INPUTS=[0b1111111100000000, 0b1111000011110000, 0b1100110011001100, 0b1010101010101010]
OUTPUTS=[0b1001001101101100, 0b0101101001011010] # high, low
BITS=16
add_always_false=True
add_always_true=True
#add_always_false=False
#add_always_true=False
avail=[I_AND, I_OR, I_XOR, I_NOT]
#avail=[I_NOR3]
"""

"""
#7-segment display
INPUTS=[0b1111111100000000, 0b1111000011110000, 0b1100110011001100, 0b1010101010101010]
# "g" segment, like here: http://www.nutsvolts.com/uploads/wygwam/NV_0501_Marston_Figure02.jpg
OUTPUTS=[0b1110111101111100] # g
BITS=16
add_always_false=False
add_always_true=False
avail=[I_AND, I_OR, I_XOR, I_NOT]
#avail=[I_NOR3]
"""

MAX_STEPS=20

# if additional always-false or always-true must be present:
if add_always_false:
    INPUTS.append(0)
if add_always_true:
    INPUTS.append(2**BITS-1)

# this called during self-testing:
def eval_ins(R, s, m, STEPS, op, op1_reg, op2_reg, op3_reg):
    op_n=m[op[s]].as_long()
    op1_reg_tmp=m[op1_reg[s]].as_long()
    op1_val=R[op1_reg_tmp]
    op2_reg_tmp=m[op2_reg[s]].as_long()
    op3_reg_tmp=m[op3_reg[s]].as_long()
    if op_n in [I_AND, I_OR, I_XOR, I_NOR3]:
        op2_val=R[op2_reg_tmp]
    if op_n==I_AND:
        return op1_val&op2_val

    elif op_n==I_OR:
        return op1_val|op2_val

    elif op_n==I_XOR:
        return op1_val^op2_val

    elif op_n==I_NOT:
        return ~op1_val

    elif op_n==I_NOR3:
        op3_val=R[op3_reg_tmp]
        return ~(op1_val|op2_val|op3_val)

    else:
        raise AssertionError

# evaluate program we've got. for self-testing.
def eval_pgm(m, STEPS, op, op1_reg, op2_reg, op3_reg):
    R=[None]*STEPS
    for i in range(len(INPUTS)):
        R[i]=INPUTS[i]

    for s in range(len(INPUTS),STEPS):
        R[s]=eval_ins(R, s, m, STEPS, op, op1_reg, op2_reg, op3_reg)

    return R

# get all states, for self-testing:
def selftest(m, STEPS, op, op1_reg, op2_reg, op3_reg):
    l=eval_pgm(m, STEPS, op, op1_reg, op2_reg, op3_reg)
    print "simulate:"
    for i in range(len(l)):
        print "r%d=" % i, format(l[i] & 2**BITS-1, '0'+str(BITS)+'b')

"""
selector() functions generates expression like:

If(op1_reg_s5 == 0,
   S_s0,
   If(op1_reg_s5 == 1,
      S_s1,
      If(op1_reg_s5 == 2,
         S_s2,
         If(op1_reg_s5 == 3,
            S_s3,
            If(op1_reg_s5 == 4,
               S_s4,
               If(op1_reg_s5 == 5,
                  S_s5,
                  If(op1_reg_s5 == 6,
                     S_s6,
                     If(op1_reg_s5 == 7,
                        S_s7,
                        If(op1_reg_s5 == 8,
                           S_s8,
                           If(op1_reg_s5 == 9,
                              S_s9,
                              If(op1_reg_s5 == 10,
                                 S_s10,
                                 If(op1_reg_s5 == 11,
                                    S_s11,
                                    0))))))))))))

this is like multiplexer or switch()
"""
def selector(R, s):
    t=0 # default value
    for i in range(MAX_STEPS):
        t=If(s==(MAX_STEPS-i-1), R[MAX_STEPS-i-1], t)
    return t

def simulate_op(R, op, op1_reg, op2_reg, op3_reg):
    op1_val=selector(R, op1_reg)
    return If(op==I_AND, op1_val & selector(R, op2_reg),
           If(op==I_OR, op1_val | selector(R, op2_reg),
           If(op==I_XOR, op1_val ^ selector(R, op2_reg),
           If(op==I_NOT, ~op1_val,
           If(op==I_NOR3, ~(op1_val | selector(R, op2_reg) | selector (R, op3_reg)),
               0))))) # default

op_to_str_tbl=["AND", "OR", "XOR", "NOT", "NOR3"]

def print_model(m, R, STEPS, op, op1_reg, op2_reg, op3_reg):
    print "%d instructions" % (STEPS-len(INPUTS))
    for s in range(STEPS):
        if s<len(INPUTS):
            t="r%d=input" % s
        else:
            op_n=m[op[s]].as_long()
            op_s=op_to_str_tbl[op_n]
            op1_reg_n=m[op1_reg[s]].as_long()
            op2_reg_n=m[op2_reg[s]].as_long()
            op3_reg_n=m[op3_reg[s]].as_long()
            if op_n in [I_AND, I_OR, I_XOR]:
                t="r%d=%s r%d, r%d" % (s, op_s, op1_reg_n, op2_reg_n)
            elif op_n==I_NOT:
                t="r%d=%s r%d" % (s, op_s, op1_reg_n)
            else: # else NOR3
                t="r%d=%s r%d, r%d, r%d" % (s, op_s, op1_reg_n, op2_reg_n, op3_reg_n)

        tt=format(m[R[s]].as_long(), '0'+str(BITS)+'b')
        print t+" "*(25-len(t))+tt

def attempt(STEPS):
    print "attempt, STEPS=", STEPS
    sl=Solver()

    # state of each register:
    R=[BitVec(('S_s%d' % s), BITS) for s in range(MAX_STEPS)]
    # operation type and operands for each register:
    op=[Int('op_s%d' % s) for s in range(MAX_STEPS)]
    op1_reg=[Int('op1_reg_s%d' % s) for s in range(MAX_STEPS)]
    op2_reg=[Int('op2_reg_s%d' % s) for s in range(MAX_STEPS)]
    op3_reg=[Int('op3_reg_s%d' % s) for s in range(MAX_STEPS)]
        
    for s in range(len(INPUTS), STEPS):
        # for each step.
        # expression like Or(op[s]==0, op[s]==1, ...) is formed here. values are taken from avail[]
        sl.add(Or(*[op[s]==j for j in avail]))
        # each operand can refer to one of registers BEFORE the current instruction:
        sl.add(And(op1_reg[s]>=0, op1_reg[s]<s))
        sl.add(And(op2_reg[s]>=0, op2_reg[s]<s))
        sl.add(And(op3_reg[s]>=0, op3_reg[s]<s))

    # fill inputs:
    for i in range(len(INPUTS)):
        sl.add(R[i]==INPUTS[i])
    # fill outputs, "must be's"
    for o in range(len(OUTPUTS)):
        sl.add(R[STEPS-(o+1)]==list(reversed(OUTPUTS))[o])

    # connect each register to "simulator":
    for s in range(len(INPUTS), STEPS):
        sl.add(R[s]==simulate_op(R, op[s], op1_reg[s], op2_reg[s], op3_reg[s]))

    tmp=sl.check()
    if tmp==sat:
        print "sat!"
        m=sl.model()
        #print m
        print_model(m, R, STEPS, op, op1_reg, op2_reg, op3_reg)
        selftest(m, STEPS, op, op1_reg, op2_reg, op3_reg)
        exit(0)
    else:
        print tmp

for s in range(len(INPUTS)+len(OUTPUTS), MAX_STEPS):
    attempt(s)

