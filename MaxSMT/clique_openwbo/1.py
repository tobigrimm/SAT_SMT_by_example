#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import my_utils, SAT_lib
import sys, re

VERTICES=50

s=SAT_lib.SAT_lib(maxsat=True)

f=open(sys.argv[1],"r")

vertices=[s.create_var() for v in range(VERTICES)]
# as much verties, as possible:
for v in range(VERTICES):
    s.fix_soft_always_true(vertices[v], 1)

edges=set()
while True:
    raw=f.readline()
    l=raw.rstrip ()
    if len(l)==0:
        break

    m=re.search('UndirectedEdge\[(.*), (.*)\]', l)
    if m!=None:
        v1=int(m.group(1))-1
        v2=int(m.group(2))-1
        edges.add((v1,v2))
        edges.add((v2,v1))

for i in range(VERTICES):
    for j in range(VERTICES):
        if i==j:
            continue
        if (i,j) not in edges:
            # if edge is present, two vertices in the pair cannot be present simultaneously:
            s.add_clause([s.neg(vertices[i]), s.neg(vertices[j])])

f.close()

print "going to run open-wbo"
if s.solve()==False:
    print ("unsat")
    exit(0)
else:
    print ("sat")

print ("")

for v in range(VERTICES):
    val=s.get_var_from_solution(vertices[v])
    if val!=0:
        print v+1

