#!/usr/bin/env python

from z3 import *

init_X, init_Y=BitVecs('init_X init_Y', 32)

X, Y=init_X, init_Y

X=X^Y
Y=Y^X
X=X^Y

print "X=", X
print "Y=", Y

s=Solver()

s.add(init_X^init_Y != X^Y)
print s.check()

