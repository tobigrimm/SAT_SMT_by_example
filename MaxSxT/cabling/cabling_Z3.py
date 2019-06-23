#!/usr/bin/env python

from z3 import *

# it's like abs(x-y)
# but since we don't have abs() here, we're going to use If():
def diff(x, y):
    return If(x<y, y-x, x-y)

A, B, C, D, E, F, G, H = Ints("A B C D E F G H")

s=Optimize()

# only 8 1U slots in rack:
s.add(And(A>=0, A<=7))
s.add(And(B>=0, B<=7))
s.add(And(C>=0, C<=7))
s.add(And(D>=0, D<=7))
s.add(And(E>=0, E<=7))
s.add(And(F>=0, F<=7))
s.add(And(G>=0, G<=7))
s.add(And(H>=0, H<=7))

# all "devices" has to be in distinct positions in the rack:
s.add(Distinct(A, B, C, D, E, F, G, H))

# A <--- 1 cable  ---> H
diff_A_H=Int("diff_A_H")
s.add(diff_A_H==diff(A,H))

# A <--- 2 cables ---> E
diff_A_E=Int("diff_A_E")
s.add(diff_A_E==diff(A,E))

# B <--- 4 cables ---> F
diff_B_F=Int("diff_B_F")
s.add(diff_B_F==diff(B,F))

# C <--- 1 cable  ---> G
diff_C_G=Int("diff_C_G")
s.add(diff_C_G==diff(C,G))

# C <--- 1 cable  ---> D
diff_C_D=Int("diff_C_D")
s.add(diff_C_D==diff(C,D))

# C <--- 1 cable  ---> E
diff_C_E=Int("diff_C_E")
s.add(diff_C_E==diff(C,E))

# D <--- 3 cables ---> H
diff_D_H=Int("diff_D_H")
s.add(diff_D_H==diff(D,H))

# G <--- 1 cable  ---> H
diff_G_H=Int("diff_G_H")
s.add(diff_G_H==diff(G,H))

final_sum=Int("final_sum")
s.add(final_sum==diff_A_H + diff_A_E*2 + diff_B_F*4 + diff_C_G + diff_C_D + diff_C_E + diff_D_H*3 + diff_G_H)

s.minimize(final_sum)
#s.maximize(final_sum)

print s.check()
m=s.model()
print m

a={}

print "order:"
a[m[A].as_long()]="A"
a[m[B].as_long()]="B"
a[m[C].as_long()]="C"
a[m[D].as_long()]="D"
a[m[E].as_long()]="E"
a[m[F].as_long()]="F"
a[m[G].as_long()]="G"
a[m[H].as_long()]="H"
for i in range(8):
    print a[i]
print "final_sum", m[final_sum]

