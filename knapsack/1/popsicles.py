from z3 import *

box1pop, box3pop, box5pop = Ints('box1pop box3pop box5pop')
pop_total = Int('pop_total')
cost_total = Int('cost_total')

s=Optimize()

s.add(pop_total == box1pop*1 + box3pop*3 + box5pop*5)
s.add(cost_total == box1pop*1 + box3pop*2 + box5pop*3)

s.add(cost_total==8)

s.add(box1pop>=0)
s.add(box3pop>=0)
s.add(box5pop>=0)

s.maximize(pop_total)

print s.check()
print s.model()

