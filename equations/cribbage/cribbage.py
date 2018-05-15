#!/usr/bin/env python

from z3 import *

def attempt(terms, N):
    #print "terms = %d" % terms

    cells=[Int('%d' % i) for i in range(terms)]

    s=Solver()

    for i in range(terms-1):
       s.add(cells[i]+1 == cells[i+1])

    s.add(Sum(cells)==N)

    s.add(cells[0]>0)

    if s.check()==sat:
        m=s.model()
        print "(%d terms) %d + ... + %d == %d" % (terms, m[cells[0]].as_long(), m[cells[terms-1]].as_long(), N)

#N=15
N=1050

for i in range(2,N):
    attempt(i, N)

