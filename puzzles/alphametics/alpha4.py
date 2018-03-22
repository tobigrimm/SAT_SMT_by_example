from z3 import *

# KNIFE+FORK+SPOON+SOUP = SUPPER

E, F, I, K, N, O, P, R, S, U = Ints('E F I K N O P R S U')

s=Solver()

s.add(Distinct(E, F, I, K, N, O, P, R, S, U))
s.add(And(E>=0, E<=9))
s.add(And(F>=0, F<=9))
s.add(And(I>=0, I<=9))
s.add(And(K>=0, K<=9))
s.add(And(N>=0, N<=9))
s.add(And(O>=0, O<=9))
s.add(And(P>=0, P<=9))
s.add(And(R>=0, R<=9))
s.add(And(S>=0, S<=9))
s.add(And(U>=0, U<=9))

#s.add(S!=0)

KNIFE, FORK, SPOON, SOUP, SUPPER = Ints('KNIFE FORK SPOON SOUP SUPPER')

# construct expression in form like:
# 10000000*L+1000000*U+100000*N+10000*C+1000*H+100*E+10*O+N
def list_to_expr(lst):
    coeff=1
    _sum=0
    for var in lst[::-1]:
        _sum=_sum+var*coeff
        coeff=coeff*10
    return _sum

s.add(KNIFE==list_to_expr([K,N,I,F,E]))
s.add(FORK==list_to_expr([F,O,R,K]))
s.add(SPOON==list_to_expr([S,P,O,O,N]))
s.add(SOUP==list_to_expr([S,O,U,P]))
s.add(SUPPER==list_to_expr([S,U,P,P,E,R]))

s.add(KNIFE+FORK+SPOON+SOUP == SUPPER)

print s.check()
print s.model()

