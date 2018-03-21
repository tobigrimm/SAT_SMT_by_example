#!/usr/bin/env python3

from z3 import *

BITS=5

# how many times a run of bits for each bit can be changed (max).
# it can be 4 for 4-bit Gray code or 8 for 5-bit code.
# 12 for 6-bit code (maybe even less)
CHANGES_MAX=8

ROWS=2**BITS
MASK=ROWS-1 # 0x1f for 5 bits, 0xf for 4 bits, etc

def bool_to_int (b):
    if b==True:
        return 1
    return 0

s=Solver()

# add a constraint: Hamming distance between two bitvectors must be 1
# i.e., two bitvectors can differ in only one bit.
# for 4 bits it works like that:
#    s.add(Or(
#        And(a3!=b3,a2==b2,a1==b1,a0==b0),
#        And(a3==b3,a2!=b2,a1==b1,a0==b0),
#        And(a3==b3,a2==b2,a1!=b1,a0==b0),
#        And(a3==b3,a2==b2,a1==b1,a0!=b0)))
def hamming1(l1, l2):
    assert len(l1)==len(l2)
    r=[]
    for i in range(len(l1)):
        t=[]
        for j in range(len(l1)):
            if i==j:
                t.append(l1[j]!=l2[j])
            else:
                t.append(l1[j]==l2[j])
        r.append(And(t))
    s.add(Or(r))

# add a constraint: bitvectors must be different.
# for 4 bits works like this:
#    s.add(Or(a3!=b3, a2!=b2, a1!=b1, a0!=b0))
def not_eq(l1, l2):
    assert len(l1)==len(l2)
    t=[l1[i]!=l2[i] for i in range(len(l1))]
    s.add(Or(t))

code=[[Bool('code_%d_%d' % (r,c)) for c in range(BITS)] for r in range(ROWS)]
ch=[[Bool('ch_%d_%d' % (r,c)) for c in range(BITS)] for r in range(ROWS)]

# each rows must be different from a previous one and a next one by 1 bit:
for i in range(ROWS):
    # get bits of the current row:
    lst1=[code[i][bit] for bit in range(BITS)]
    # get bits of the next row.
    # important: if the current row is the last one, (last+1)&MASK==0, so we overlap here:
    lst2=[code[(i+1)&MASK][bit] for bit in range(BITS)]
    hamming1(lst1, lst2)

# no row must be equal to any another row:
for i in range(ROWS):
    for j in range(ROWS):
        if i==j:
            continue
        lst1=[code[i][bit] for bit in range(BITS)]
        lst2=[code[j][bit] for bit in range(BITS)]
        not_eq(lst1, lst2)

# 1 in ch[] table means that run of 1's has been changed to run of 0's, or back.
# "run" change detected using simple XOR:
for i in range(ROWS):
    for bit in range(BITS):
        # row overlapping works here as well:
        s.add(ch[i][bit]==Xor(code[i][bit],code[(i+1)&MASK][bit]))

# only CHANGES_MAX of 1 bits is allowed in ch[] table for each bit:
for bit in range(BITS):
    t=[ch[i][bit] for i in range(ROWS)]
    # this is a dirty hack.
    # AtMost() takes arguments like:
    # AtMost(v1, v2, v3, v4, 2) <- this means, only 2 booleans (or less) from the list can be True.
    # but we need to pass a list here.
    # so a CHANGES_MAX number is appended to a list and a new list is then passed as arguments list:
    s.add(AtMost(*(t+[CHANGES_MAX])))

result=s.check()
if result==unsat:
    exit(0)
m=s.model()

# get the model.

print ("code table:")

for i in range(ROWS):
    t=""
    for bit in range(BITS):
        # comma at the end means "no newline":
        t=t+str(bool_to_int(is_true(m[code[i][BITS-1-bit]])))+" "
    print (t)

print ("ch table:")

stat={}

for i in range(ROWS):
    t=""
    for bit in range(BITS):
        x=is_true(m[ch[i][BITS-1-bit]])
        if x:
            # increment if bit is present in dict, set 1 if not present
            stat[bit]=stat.get(bit, 0)+1
        # comma at the end means "no newline":
        t=t+str(bool_to_int(x))+" "
    print (t)

print ("stat (bit number: number of changes): ", stat)

