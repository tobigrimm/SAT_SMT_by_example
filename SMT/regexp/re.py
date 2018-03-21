#!/usr/bin/env python
from z3 import *

INVALID_STATE=999
ACCEPTING_STATES=[13, 19, 23, 24]

# s - state
# i - input character
def transition (s, i):
    # this is like switch()
    return If(And(s==0, i==ord('r')), 3,
    If(And(s==0, i==ord('b')), 4,
    If(And(s==0, i==ord('g')), 5,
    If(And(s==0, i==ord('d')), 1,
    If(And(s==0, i==ord('l')), 2,
    If(And(s==1, i==ord('a')), 6,
    If(And(s==2, i==ord('i')), 7,
    If(And(s==3, i==ord('e')), 8,
    If(And(s==4, i==ord('l')), 9,
    If(And(s==5, i==ord('r')), 10,
    If(And(s==6, i==ord('r')), 11,
    If(And(s==7, i==ord('g')), 12,
    If(And(s==8, i==ord('d')), 13,
    If(And(s==9, i==ord('u')), 14,
    If(And(s==10, i==ord('e')), 15,
    If(And(s==11, i==ord('k')), 16,
    If(And(s==12, i==ord('h')), 17,
    If(And(s==13, i==ord('i')), 18,
    If(And(s==14, i==ord('e')), 19,
    If(And(s==15, i==ord('e')), 20,
    If(And(s==16, i==ord('r')), 3,
    If(And(s==16, i==ord('b')), 4,
    If(And(s==16, i==ord('g')), 5,
    If(And(s==17, i==ord('t')), 21,
    If(And(s==18, i==ord('s')), 22,
    If(And(s==19, i==ord('i')), 18,
    If(And(s==20, i==ord('n')), 23,
    If(And(s==21, i==ord('r')), 3,
    If(And(s==21, i==ord('b')), 4,
    If(And(s==21, i==ord('g')), 5,
    If(And(s==22, i==ord('h')), 24,
    If(And(s==23, i==ord('i')), 18,
        INVALID_STATE))))))))))))))))))))))))))))))))

def print_model(m, length, inputs):
    #print "length=", length
    tmp=""
    for i in range(length-1):
        tmp=tmp+chr(m[inputs[i]].as_long())
    print tmp

def make_FSM(length):
    s=Solver()
    states=[Int('states_%d' % i) for i in range(length)]
    inputs=[Int('inputs_%d' % i) for i in range(length-1)]

    # initial state:
    s.add(states[0]==0)

    # the last state must be equal to one of the acceping states
    s.add(Or(*[states[length-1]==i for i in ACCEPTING_STATES]))

    # all states are in limits...
    for i in range(length):
        s.add(And(states[i]>=0, states[i]<=24))
        # redundant, though. however, we are not interesting in non-matched inputs, right?
        s.add(states[i]!=INVALID_STATE)

    # "insert" transition() functions between subsequent states
    for i in range(length-1):
        s.add(states[i+1] == transition(states[i], inputs[i]))

    # enumerate results:
    results=[]
    while s.check()==sat:
        m=s.model()
        print_model(m, length, inputs)
        results.append(m)
        block = []
        for d in m:
            c=d()
            block.append(c != m[d])
        s.add(Or(block))

for l in range(2,15):
    make_FSM(l)

