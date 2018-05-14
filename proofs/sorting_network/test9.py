from z3 import *

a, b, c, d, e, f, g, h, i=Ints('a b c d e f g h i')

def Z3_min (a, b):
    return If(a<b, a, b)

def Z3_max (a, b):
    return If(a>b, a, b)

def comparator (a, b):
    return (Z3_min(a, b), Z3_max(a, b))

def line(lst, params):
    rt=lst
    start=0
    while start+1 < len(params):
        try:
            first=params.index("+", start)
        except ValueError:
            # no more "+" in parameter string
            return rt
        second=params.index("+", first+1)
        rt[first], rt[second]=comparator(lst[first], lst[second])
        start=second+1
    # parameter string ended
    return rt

l=[i, h, g, f, e, d, c, b, a]
l=line(l, " ++++++++") 
l=line(l, " + + + + ") 
l=line(l, "   +   + ") 
l=line(l, " +   +   ") 
l=line(l, "+      + ") 
l=line(l, "  + + + +") 
l=line(l, "    +   +") 
l=line(l, "  +   +  ") 
l=line(l, "    + +  ") 
l=line(l, "   + +++ ") 
l=line(l, "+   +    ")
l=line(l, "+ + + +  ") 
l=line(l, "+  +     ") 
l=line(l, "  +  +   ") 
l=line(l, "++++++ ++") 

# construct expression like And(..., k[2]>=k[1], k[1]>=k[0])
expr=[(l[k+1]>=l[k]) for k in range(len(l)-1)]

# True if everything works correctly:
correct=And(*expr)

s=Solver()

# we want to find inputs for which correct==False:
s.add(Not(correct))
print s.check() # must be unsat

