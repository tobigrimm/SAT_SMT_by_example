#!/usr/bin/env python

import math, SAT_lib, random

SIZE=8

# generate random 8*8 input:
initial=[[random.randint(0,1) for r in range(SIZE)] for c in range(SIZE)]

print "initial (random):"
s=0
for r in range(SIZE):
    for c in range(SIZE):
        print initial[r][c],
        s=s+initial[r][c]
    print ""
print "total=",s
print ""

"""
# test:
initial=[
    [0,0,0,0,0,1,0,0],
    [0,0,0,0,0,1,0,0],
    [0,0,0,0,0,1,0,0],
    [0,0,0,0,0,1,0,0],
    [1,1,1,1,1,1,1,1],
    [0,0,0,0,0,1,0,0],
    [0,0,0,0,0,1,0,0],
    [0,0,0,0,0,1,0,0]]
"""

def do_all(STEPS):

    # this is MaxSAT problem:
    s=SAT_lib.SAT_lib(True)

    STATES=STEPS+1

    # bool variables for all 64 cells for all states:
    states=[[[s.create_var() for r in range(SIZE)] for c in range(SIZE)] for st in range(STATES)]

    # for all states:
    # False - horizontal, True - vertical:
    H_or_V=[s.create_var() for i in range(STEPS)]
    # this is "shared" variable, can hold both and or column:
    row_col=[[s.create_var() for r in range(SIZE)] for i in range(STEPS)]

    # set variables on state #0:
    for r in range(SIZE):
        for c in range(SIZE):
            s.fix(states[0][r][c], initial[r][c])

    # each row_col bitvector can only hold one single bit:
    for st in range(STEPS):
        s.make_one_hot(row_col[st])

    # now this is the essence of the problem.
    # each bit is flipped if H_or_V[]==False AND row_col[] is equal to its row
    # ... OR H_or_V[]==True AND row_col[] is equal to its column
    for st in range(STEPS):
        for r in range(SIZE):
            for c in range(SIZE):
                cond1=s.AND(s.NOT(H_or_V[st]), row_col[st][r])
                cond2=s.AND(H_or_V[st], row_col[st][c])
                bit=s.OR_list([cond1,cond2])

                s.fix(s.EQ(states[st+1][r][c], s.XOR(states[st][r][c], bit)), True)

    # soft constraint: unlike hard constraints, they may be satisfied, or may be not, 
    # but MaxSAT solver's task is to find a solution, where maximum of soft clauses will be satisfied:
    for r in range(SIZE):
        for c in range(SIZE):
            s.fix_soft(states[STEPS][r][c], False, 1)
            # set to True if you like to find solution with the most cells set to 1:
            #s.fix_soft(states[STEPS][r][c], True, 1)

    assert s.solve()==True

    # get solution:
    total=0
    for r in range(SIZE):
        for c in range(SIZE):
            t=s.get_var_from_solution(states[STEPS][r][c])
            print t,
            total=total+t
        print ""
    print "total=", total

    for st in range(STEPS):
        if s.get_var_from_solution(H_or_V[st]):
            print "vertical, ",
        else:
            print "horizontal, ",
        print int(math.log(SAT_lib.BV_to_number(s.get_BV_from_solution(row_col[st])), 2))

for s in range(1,5+1):
    print "trying %d steps" % s
    do_all(s)
    print ""

