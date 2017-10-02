#!/usr/bin/env python3

import subprocess, os, itertools
import frolic, Xu

BITS=5

# how many times a run of bits for each bit can be changed (max).
# it can be 4 for 4-bit Gray code or 8 for 5-bit code.
# 12 for 6-bit code (maybe even less)

ROWS=2**BITS
MASK=ROWS-1 # 0x1f for 5 bits, 0xf for 4 bits, etc

def do_all():
    s=Xu.Xu(maxsat=True)

    code=[s.alloc_BV(BITS) for r in range(ROWS)]
    ch=[s.alloc_BV(BITS) for r in range(ROWS)]

    # each rows must be different from a previous one and a next one by 1 bit:
    for i in range(ROWS):
        # get bits of the current row:
        lst1=[code[i][bit] for bit in range(BITS)]
        # get bits of the next row.
        # important: if the current row is the last one, (last+1)&MASK==0, so we overlap here:
        lst2=[code[(i+1)&MASK][bit] for bit in range(BITS)]
        s.hamming1(lst1, lst2)

    # no row must be equal to any another row:
    for i in range(ROWS):
        for j in range(ROWS):
            if i==j:
                continue
            lst1=[code[i][bit] for bit in range(BITS)]
            lst2=[code[j][bit] for bit in range(BITS)]
            s.fix_BV_NEQ(lst1, lst2)

    # 1 in ch[] table means that run of 1's has been changed to run of 0's, or back.
    # "run" change detected using simple XOR:
    for i in range(ROWS):
        for bit in range(BITS):
            # row overlapping works here as well.
            # we add here "soft" constraint with weight=1:
            s.fix_soft(s.EQ(ch[i][bit], s.XOR(code[i][bit],code[(i+1)&MASK][bit])), False, weight=1)

    if s.solve()==False:
        print ("unsat")
        exit(0)

    print ("code table:")

    for i in range(ROWS):
        tmp=""
        for bit in range(BITS):
            t=s.get_var_from_solution(code[i][BITS-1-bit])
            if t:
                tmp=tmp+"*"
            else:
                tmp=tmp+" "
        print (tmp)

    # get statistics:
    stat={}
    
    for i in range(ROWS):
        for bit in range(BITS):
            x=s.get_var_from_solution(ch[i][BITS-1-bit])
            if x==0:
                # increment if bit is present in dict, set 1 if not present
                stat[bit]=stat.get(bit, 0)+1
    
    print ("stat (bit number: number of changes): ")
    print (stat)

do_all()

