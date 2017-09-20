from z3 import *

# VIOLIN+VIOLIN+VIOLA = TRIO+SONATA

A, I, L, N, O, R, S, T, V = Ints('A, I, L, N, O, R, S, T, V')

s=Solver()

s.add(Distinct(A, I, L, N, O, R, S, T, V))
s.add(And(A>=0, A<=9))
s.add(And(I>=0, I<=9))
s.add(And(L>=0, L<=9))
s.add(And(N>=0, N<=9))
s.add(And(O>=0, O<=9))
s.add(And(R>=0, R<=9))
s.add(And(S>=0, S<=9))
s.add(And(T>=0, T<=9))
s.add(And(V>=0, V<=9))

VIOLIN, VIOLA, SONATA, TRIO = Ints('VIOLIN, VIOLA, SONATA, TRIO')

s.add(VIOLIN==100000*V+10000*I+1000*O+100*L+10*I+N)
s.add(VIOLA==10000*V+1000*I+100*O+10*L+A)
s.add(SONATA==100000*S+10000*O+1000*N+100*A+10*T+A)
s.add(TRIO==1000*T+100*R+10*I+O)

s.add(VIOLIN+VIOLIN+VIOLA == TRIO+SONATA)

print s.check()
print s.model()

