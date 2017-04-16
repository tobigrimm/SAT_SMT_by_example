#!/usr/bin/python

import subprocess

def mathematica_to_CNF (s, a):
    s=s.replace("a", a[0]).replace("b", a[1]).replace("c", a[2]).replace("d", a[3])
    s=s.replace("e", a[4]).replace("f", a[5]).replace("g", a[6]).replace("h", a[7])
    s=s.replace("!", "-").replace("||", " ").replace("(", "").replace(")", "")
    s=s.split ("&&")
    return s

def POPCNT2 (a):
    s="(!a||!b||!c)&&(!a||!b||!d)&&(!a||!b||!e)&&(!a||!b||!f)&&(!a||!b||!g)&&(!a||!b||!h)&&(!a||!c||!d)&&" \
      "(!a||!c||!e)&&(!a||!c||!f)&&(!a||!c||!g)&&(!a||!c||!h)&&(!a||!d||!e)&&(!a||!d||!f)&&(!a||!d||!g)&&" \
      "(!a||!d||!h)&&(!a||!e||!f)&&(!a||!e||!g)&&(!a||!e||!h)&&(!a||!f||!g)&&(!a||!f||!h)&&(!a||!g||!h)&&" \
      "(a||b||c||d||e||f||g)&&(a||b||c||d||e||f||h)&&(a||b||c||d||e||g||h)&&(a||b||c||d||f||g||h)&&" \
      "(a||b||c||e||f||g||h)&&(a||b||d||e||f||g||h)&&(a||c||d||e||f||g||h)&&(!b||!c||!d)&&(!b||!c||!e)&&" \
      "(!b||!c||!f)&&(!b||!c||!g)&&(!b||!c||!h)&&(!b||!d||!e)&&(!b||!d||!f)&&(!b||!d||!g)&&(!b||!d||!h)&&" \
      "(!b||!e||!f)&&(!b||!e||!g)&&(!b||!e||!h)&&(!b||!f||!g)&&(!b||!f||!h)&&(!b||!g||!h)&&(b||c||d||e||f||g||h)&&" \
      "(!c||!d||!e)&&(!c||!d||!f)&&(!c||!d||!g)&&(!c||!d||!h)&&(!c||!e||!f)&&(!c||!e||!g)&&(!c||!e||!h)&&" \
      "(!c||!f||!g)&&(!c||!f||!h)&&(!c||!g||!h)&&(!d||!e||!f)&&(!d||!e||!g)&&(!d||!e||!h)&&(!d||!f||!g)&&" \
      "(!d||!f||!h)&&(!d||!g||!h)&&(!e||!f||!g)&&(!e||!f||!h)&&(!e||!g||!h)&&(!f||!g||!h)"
    return mathematica_to_CNF(s, a)

clauses=POPCNT2(["1","2","3","4","5","6","7","8"])

f=open("tmp.cnf", "w")
f.write ("p cnf 8 "+str(len(clauses))+"\n")
for c in clauses:
    f.write(c+" 0\n")
f.close()

