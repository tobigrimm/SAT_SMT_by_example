#!/usr/bin/env python

import itertools
from z3 import *

# 7 peoples, 6 committees

S={}
S[1]=set([1, 2, 3])
S[2]=set([2, 3, 4])
S[3]=set([3, 4, 5])
S[4]=set([4, 5, 6])
S[5]=set([5, 6, 7])
S[6]=set([1, 6, 7])

committees=len(S)

s=Solver()

Color_or_Hour=[Int('Color_or_hour_%d' % i) for i in range(committees)]

# enumerate all possible pairs of committees:
for pair in itertools.combinations(S, r=2):
    # if intersection of two sets has *something* (i.e., if two committees has at least one person in common):
    if len(S[pair[0]] & S[pair[1]])>0:
        # ... add an edge between vertices (or persons) -- these colors (or hours) must differ:
        s.add(Color_or_Hour[pair[0]-1] != Color_or_Hour[pair[1]-1])

# limit all colors (or hours) in 0..2 range (3 colors/hours):
for i in range(committees):
    s.add(And(Color_or_Hour[i]>=0, Color_or_Hour[i]<=2))

assert s.check()==sat
m=s.model()
#print m

schedule={}

for i in range(committees):
    hour=m[Color_or_Hour[i]].as_long()
    if hour not in schedule:
        schedule[hour]=[]
    schedule[hour].append(i+1)

for t in schedule:
    print "hour:", t, "committees:", schedule[t]

