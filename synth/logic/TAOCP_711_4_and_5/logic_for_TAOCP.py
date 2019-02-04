#!/usr/bin/env python
from z3 import *
import sys

I_AND, I_OR, I_XOR, I_NOT, I_NOR3, I_NAND, I_ANDN = 0,1,2,3,4,5,6

# 2-input function
BITS=4
add_always_false=False
add_always_true=False
#add_always_false=True
#add_always_true=True
avail=[I_NAND]
#avail=[I_ANDN]

MAX_STEPS=10

# My representation of TT is: [MSB..LSB].
# Knuth's representation in the section 7.1.1 (Boolean basics) of TAOCP is different: [LSB..MSB].
# so I'll reverse bits before printing TT:
def rvr_4_bits(i):
    return ((i>>0)&1)<<3 | ((i>>1)&1)<<2 | ((i>>2)&1)<<1 | ((i>>3)&1)<<0

def find_NAND_only_for_TT (OUTPUTS):
    INPUTS=[0b1100, 0b1010]
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
        if op_n in [I_AND, I_OR, I_XOR, I_NOR3, I_NAND, I_ANDN]:
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
        elif op_n==I_NAND:
            return ~(op1_val&op2_val)
        elif op_n==I_ANDN:
            return (~op1_val)&op2_val
    
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
    selector() function generates expression like:
    
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
               If(op==I_NAND, ~(op1_val & selector(R, op2_reg)),
               If(op==I_ANDN, (~op1_val) & selector(R, op2_reg),
                   0))))))) # default
    
    op_to_str_tbl=["AND", "OR", "XOR", "NOT", "NOR3", "NAND", "ANDN"]
    
    def print_model(m, R, STEPS, op, op1_reg, op2_reg, op3_reg):
        print ("%d instructions for OUTPUTS TT (Knuth's representation)=" % (STEPS-len(INPUTS))), format(rvr_4_bits(OUTPUTS[0]) & 2**BITS-1, '0'+str(BITS)+'b')
        for s in range(STEPS):
            if s<len(INPUTS):
                t="r%d=input" % s
            else:
                op_n=m[op[s]].as_long()
                op_s=op_to_str_tbl[op_n]
                op1_reg_n=m[op1_reg[s]].as_long()
                op2_reg_n=m[op2_reg[s]].as_long()
                op3_reg_n=m[op3_reg[s]].as_long()
                if op_n in [I_AND, I_OR, I_XOR, I_NAND, I_ANDN]:
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
            return True
        else:
            print tmp
        return False
    
    for s in range(len(INPUTS)+len(OUTPUTS), MAX_STEPS):
        if attempt(s):
            return

for i in range(16):
    print "getting circuit for TT=", format(i & 2**BITS-1, '0'+str(BITS)+'b')
    find_NAND_only_for_TT ([i])

