#!/usr/bin/env python3

from z3 import *

fg, fi, tg, ti, eg, ei = Bools('fg fi tg ti eg ei')

s=Solver()

s.add(fg!=fi)
s.add(tg!=ti)
s.add(eg!=ei)

s.add(ei==And(fg, ti))

s.add(fi==Implies(eg, tg))
#s.add(fi==Or(Not(eg), tg)) # Or(-x, y) is the same as Implies

s.add(ti==And(ti, Or(fg, eg)))

print (s.check())
print (s.model())

