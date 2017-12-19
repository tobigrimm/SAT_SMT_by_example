from z3 import *

# H+E+L+L+O = W+O+R+L+D = 25

H, E, L, O, W, R, D = Ints ('H E L O W R D')

s=Solver()

s.add(Distinct(H, E, L, O, W, R, D))
s.add(And(H>=1, H<=9))
s.add(And(E>=1, E<=9))
s.add(And(L>=1, L<=9))
s.add(And(O>=1, O<=9))
s.add(And(W>=1, W<=9))
s.add(And(R>=1, R<=9))
s.add(And(D>=1, D<=9))

s.add(H+E+L+L+O == 25)
s.add(W+O+R+L+D == 25)

print s.check()
print s.model()

