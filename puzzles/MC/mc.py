#!/usr/bin/env python

from z3 import *

a, b, c, d, e, f = Bools('a b c d e f')

s=Solver()

s.add(a==And(b,c,d,e,f))
s.add(b==And(Not(c),Not(d),Not(e),Not(f)))
s.add(c==And(a,b))
s.add(d==Or(And(a,Not(b),Not(c)), And(Not(a),b,Not(c)), And(Not(a),Not(b),c)))
s.add(e==And(Not(a),Not(b),Not(c),Not(d)))
s.add(f==And(Not(a),Not(b),Not(c),Not(d), Not(e)))

print s.check()
print s.model()

