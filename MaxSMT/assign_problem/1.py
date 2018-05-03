#!/usr/bin/env python

from z3 import *

# this is optimization problem:
s=Optimize()

choice=[Int('choice_%d' % i) for i in range(3)]
row_value=[Int('row_value_%d' % i) for i in range(3)]

for i in range(3):
    s.add(And(choice[i]>=0, choice[i]<=2))

s.add(Distinct(choice))
s.add(row_value[0]==
	If(choice[0]==0, 250, 
	If(choice[0]==1, 400, 
	If(choice[0]==2, 350, -1))))

s.add(row_value[1]==
	If(choice[1]==0, 400, 
	If(choice[1]==1, 600, 
	If(choice[1]==2, 350, -1))))

s.add(row_value[2]==
	If(choice[2]==0, 200, 
	If(choice[2]==1, 400, 
	If(choice[2]==2, 250, -1))))

final_sum=Int('final_sum')

# final_sum equals to sum of all row_value[] values:
s.add(final_sum==Sum(*row_value))

# find such a (distinct) choice[]'s, so that the final_sum would be minimal:
s.minimize(final_sum)

print s.check()
print s.model()

