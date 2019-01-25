#!/usr/bin/env python
from z3 import *
import sys, random

BIT_WIDTH=32

MAX_STEPS=20

#CONST=0
#CONST=0x12345678
#CONST=0x0badf00d
#CONST=0xffffffff

CONST=random.randint(0,0x100000000)
print "CONST=0x%x" % CONST

CHAINS=30

def simulate_op(R, c, op, op1_val, op2_imm, STEPS):
    return If(op==0, op1_val - op2_imm,
           If(op==1, op1_val ^ op2_imm,
           If(op==2, op1_val & op2_imm,
               0))) # default

op_to_str_tbl=["SUB", "XOR", "AND"]
instructions=len(op_to_str_tbl)

def print_model(m, STEPS, op, op2_imm):
    for s in range(1,STEPS):
        op_n=m[op[s]].as_long()
        op_s=op_to_str_tbl[op_n]
        print "%s EAX, 0x%x" % (op_s, m[op2_imm[s]].as_long())

def attempt(STEPS):
    print "attempt, STEPS=", STEPS
    sl=Solver()

    R=[[BitVec('S_s%d_c%d' % (s, c), BIT_WIDTH) for s in range(MAX_STEPS)] for c in range (CHAINS)]
    op=[Int('op_s%d' % s) for s in range(MAX_STEPS)]
    op2_imm=[BitVec('op2_imm_s%d' % s, BIT_WIDTH) for s in range(MAX_STEPS)]

    for s in range(1, STEPS):
        # for each step, instruction is in 0..2 range:
        sl.add(Or(op[s]==0, op[s]==1, op[s]==2))

        # each 8-bit byte in operand must be in [0x21..0x7e] range:
        # or 0x20, if space character is tolerated...
        for shift_cnt in [0,8,16,24]:
            sl.add(And((op2_imm[s]>>shift_cnt)&0xff>=0x21),(op2_imm[s]>>shift_cnt)&0xff<=0x7e)

        """
        # or use 0..9, a..z, A..Z:
        for shift_cnt in [0,8,16,24]:
            sl.add(Or(
                And((op2_imm[s]>>shift_cnt)&0xff>=ord('0'),(op2_imm[s]>>shift_cnt)&0xff<=ord('9')),
                And((op2_imm[s]>>shift_cnt)&0xff>=ord('a'),(op2_imm[s]>>shift_cnt)&0xff<=ord('z')),
                And((op2_imm[s]>>shift_cnt)&0xff>=ord('A'),(op2_imm[s]>>shift_cnt)&0xff<=ord('Z'))))
        """

    # for all input random numbers, the result must be CONST:
    for c in range(CHAINS):
        sl.add(R[c][0]==random.randint(0,0x100000000))
        sl.add(R[c][STEPS-1]==CONST)

        for s in range(1, STEPS):
            sl.add(R[c][s]==simulate_op(R,c, op[s], R[c][s-1], op2_imm[s], STEPS))

    tmp=sl.check()
    if tmp==sat:
        print "sat!"
        m=sl.model()
        print_model(m, STEPS, op, op2_imm)
        exit(0)
    else:
        print tmp

for s in range(2, MAX_STEPS):
    attempt(s)

