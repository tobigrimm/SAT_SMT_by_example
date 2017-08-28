#!/usr/bin/env python

import re, sys
from z3 import *

TOTAL_TESTS=1000

# read gcov result and return list of lines executed:
def process_file (fname):
    lines=[]
    f=open(fname,"r")
 
    while True:
        l=f.readline().rstrip()
        m = re.search('^ *([0-9]+):  ([0-9]+):.*$', l)
        if m!=None:
            lines.append(int(m.group(2)))
        if len(l)==0:
            break

    f.close()
    return lines

# k=test number; v=list of lines executed
stat={}
for test in range(TOTAL_TESTS):
    stat[test]=process_file("compression.c.gcov."+str(test))

# that will be a list of all lines in all tests:
all_lines=set()
# k=line, v=list of tests, which trigger that line:
tests_for_line={}

for test in stat:
    all_lines|=set(stat[test])
    for line in stat[test]:
        tests_for_line[line]=tests_for_line.get(line, []) + [test]

# int variable for each test:
tests=[Int('test_%d' % (t)) for t in range(TOTAL_TESTS)]

# this is optimization problem, so Optimize() instead of Solver():
opt = Optimize()

# each test variable is either 0 (absent) or 1 (present):
for t in tests:
    opt.add(Or(t==0, t==1))

# we know which tests can trigger each line
# so we enumerate all tests when preparing expression for each line
# we form expression like "test_1==1 OR test_2==1 OR ..." for each line:
for line in list(all_lines):
    expressions=[tests[s]==1 for s in tests_for_line[line]]
    # expression is a list which unfolds as list of arguments into Z3's Or() function (see asterisk)
    # that results in big expression like "Or(test_1==1, test_2==1, ...)"
    # the expression is then added as a constraint:
    opt.add(Or(*expressions))

# we need to find a such solution, where minimal number of all "test_X" variables will have 1
# "*tests" unfolds to a list of arguments: [test_1, test_2, test_3,...]
# "Sum(*tests)" unfolds to the following expression: "Sum(test_1, test_2, ...)"
# the sum of all "test_X" variables should be as minimal as possible:
h=opt.minimize(Sum(*tests))

print (opt.check())
m=opt.model()

# print all variables set to 1:
for t in tests:
    if m[t].as_long()==1:
        print (t)

