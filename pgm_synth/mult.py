#!/usr/bin/env python
from z3 import *
import sys

MAX_STEPS=10
CHAINS=2
chain_inputs=[0,1]

def selector(R, c, s):
    # for all MAX_STEPS:
    return If(s==0, R[c][0], 
            If(s==1, R[c][1], 
            If(s==2, R[c][2], 
            If(s==3, R[c][3], 
            If(s==4, R[c][4], 
            If(s==5, R[c][5],
            If(s==6, R[c][6], 
            If(s==7, R[c][7], 
            If(s==8, R[c][8], 
            If(s==9, R[c][9], 
                0)))))))))) # default

def simulate_op(R, c, op, op1_reg, op2_reg, op2_imm):
    op1_val=selector(R,c,op1_reg)
    return If(op==0, op1_val + selector(R, c, op2_reg),
           If(op==1, op1_val - selector(R, c, op2_reg),
           If(op==2, op1_val << op2_imm,
               0))) # default

op_to_str_tbl=["ADD", "SUB", "SHL"]

def print_model(m, STEPS, op, op1_reg, op2_reg, op2_imm):
    for s in range(1,STEPS):
        op_n=m[op[s]].as_long()
        op_s=op_to_str_tbl[op_n]
        op1_reg_n=m[op1_reg[s]].as_long()
        if op_n in [0, 1]: # print ADD or SUB
            print "r%d=%s r%d, r%d" % (s, op_s, op1_reg_n, m[op2_reg[s]].as_long())
        else: # print SHL
            print "r%d=%s r%d, %d" % (s, op_s, op1_reg_n, m[op2_imm[s]].as_long())

def eval_ins(R, s, m, STEPS, op, op1_reg, op2_reg, op2_imm):
    op_n=m[op[s]].as_long()
    op1_reg_tmp=m[op1_reg[s]].as_long()
    assert R[op1_reg_tmp]!=None
    op1_val=R[op1_reg_tmp]
    op2_reg_tmp=m[op2_reg[s]].as_long()
    op2_imm_tmp=m[op2_imm[s]].as_long()
    if op_n==0: # ADD
        assert R[op2_reg_tmp]!=None
        op2_val=R[op2_reg_tmp]

        return op1_val+op2_val
    elif op_n==1: # SUB
        assert R[op2_reg_tmp]!=None
        op2_val=R[op2_reg_tmp]

        return op1_val-op2_val
    elif op_n==2: # SHL
        return op1_val << op2_imm_tmp
    else:
        raise AssertionError

def eval_chain(input, m, STEPS, op, op1_reg, op2_reg, op2_imm):
    R=[None]*STEPS
    R[0]=input
    for s in range(1,STEPS):
        R[s]=eval_ins(R, s, m, STEPS, op, op1_reg, op2_reg, op2_imm)
    return R[STEPS-1] 

def selftest(m, STEPS, op, op1_reg, op2_reg, op2_imm):
    result0=eval_chain(0, m, STEPS, op, op1_reg, op2_reg, op2_imm)
    result1=eval_chain(1, m, STEPS, op, op1_reg, op2_reg, op2_imm)
    result123=eval_chain(123, m, STEPS, op, op1_reg, op2_reg, op2_imm)
    if 0*multiplier==result0 and 1*multiplier==result1 and 123*multiplier==result123:
        print "tests are passed"
    else:
        print "tests are NOT passed"
        print "result0",result0
        print "result1",result1
        print "result123",result123

def attempt(STEPS):
    print "attempt, STEPS=", STEPS
    sl=Solver()

    R=[[BitVec('S_s%d_c%d' % (s, c), 32) for s in range(MAX_STEPS)] for c in range (CHAINS)]
    op=[Int('op_s%d' % s) for s in range(MAX_STEPS)]
    op1_reg=[Int('op1_reg_s%d' % s) for s in range(MAX_STEPS)]
    op2_reg=[Int('op2_reg_s%d' % s) for s in range(MAX_STEPS)]
    op2_imm=[BitVec('op2_imm_s%d' % s, 32) for s in range(MAX_STEPS)]

    for s in range(1, STEPS):
        # for each step
        sl.add(And(op[s]>=0, op[s]<=2))
        sl.add(And(op1_reg[s]>=0, op1_reg[s]<s))
        sl.add(And(op2_reg[s]>=0, op2_reg[s]<s))
        sl.add(And(op2_imm[s]>=1, op2_imm[s]<=31))

    for c in range(CHAINS):
        # for each chain:
        sl.add(R[c][0]==chain_inputs[c])
        sl.add(R[c][STEPS-1]==chain_inputs[c]*multiplier)

    for s in range(1, STEPS):
        sl.add(R[c][s]==simulate_op(R,c, op[s], op1_reg[s], op2_reg[s], op2_imm[s]))

    tmp=sl.check()
    if tmp==sat:
        print "sat!"
        m=sl.model()
        print_model(m, STEPS, op, op1_reg, op2_reg, op2_imm)
        selftest(m, STEPS, op, op1_reg, op2_reg, op2_imm)
        exit(0)
    else:
        print tmp

if len(sys.argv)!=2:
    print "Usage: %s <n>, where n is multiplier" % sys.argv[0]
    exit(0)

multiplier=int(sys.argv[1])

print "multiplier=", multiplier
for s in range(2, MAX_STEPS):
    attempt(s)

