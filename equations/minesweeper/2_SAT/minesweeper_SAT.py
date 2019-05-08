#!/usr/bin/python

import subprocess

WIDTH=9
HEIGHT=9
VARS_TOTAL=(WIDTH+2)*(HEIGHT+2)

known=[
"01?10001?",
"01?100011",
"011100000",
"000000000",
"111110011",
"????1001?",
"????3101?",
"?????211?",
"?????????"]

def mathematica_to_CNF (s, a):
    s=s.replace("a", a[0]).replace("b", a[1]).replace("c", a[2]).replace("d", a[3])
    s=s.replace("e", a[4]).replace("f", a[5]).replace("g", a[6]).replace("h", a[7])
    s=s.replace("!", "-").replace("||", " ").replace("(", "").replace(")", "")
    s=s.split ("&&")
    return s

def POPCNT0 (a):
    s="!a&&!b&&!c&&!d&&!e&&!f&&!g&&!h"
    return mathematica_to_CNF(s, a)

def POPCNT1 (a):
    s="(!a||!b)&&(!a||!c)&&(!a||!d)&&(!a||!e)&&(!a||!f)&&(!a||!g)&&(!a||!h)&&(a||b||c||d||e||f||g||h)&&" \
      "(!b||!c)&&(!b||!d)&&(!b||!e)&&(!b||!f)&&(!b||!g)&&(!b||!h)&&(!c||!d)&&(!c||!e)&&(!c||!f)&&(!c||!g)&&" \
      "(!c||!h)&&(!d||!e)&&(!d||!f)&&(!d||!g)&&(!d||!h)&&(!e||!f)&&(!e||!g)&&(!e||!h)&&(!f||!g)&&(!f||!h)&&(!g||!h)"
    return mathematica_to_CNF(s, a)

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

def POPCNT3 (a):
    s="(!a||!b||!c||!d)&&(!a||!b||!c||!e)&&(!a||!b||!c||!f)&&(!a||!b||!c||!g)&&(!a||!b||!c||!h)&&" \
      "(!a||!b||!d||!e)&&(!a||!b||!d||!f)&&(!a||!b||!d||!g)&&(!a||!b||!d||!h)&&(!a||!b||!e||!f)&&" \
      "(!a||!b||!e||!g)&&(!a||!b||!e||!h)&&(!a||!b||!f||!g)&&(!a||!b||!f||!h)&&(!a||!b||!g||!h)&&" \
      "(!a||!c||!d||!e)&&(!a||!c||!d||!f)&&(!a||!c||!d||!g)&&(!a||!c||!d||!h)&&(!a||!c||!e||!f)&&" \
      "(!a||!c||!e||!g)&&(!a||!c||!e||!h)&&(!a||!c||!f||!g)&&(!a||!c||!f||!h)&&(!a||!c||!g||!h)&&" \
      "(!a||!d||!e||!f)&&(!a||!d||!e||!g)&&(!a||!d||!e||!h)&&(!a||!d||!f||!g)&&(!a||!d||!f||!h)&&" \
      "(!a||!d||!g||!h)&&(!a||!e||!f||!g)&&(!a||!e||!f||!h)&&(!a||!e||!g||!h)&&(!a||!f||!g||!h)&&" \
      "(a||b||c||d||e||f)&&(a||b||c||d||e||g)&&(a||b||c||d||e||h)&&(a||b||c||d||f||g)&&(a||b||c||d||f||h)&&" \
      "(a||b||c||d||g||h)&&(a||b||c||e||f||g)&&(a||b||c||e||f||h)&&(a||b||c||e||g||h)&&(a||b||c||f||g||h)&&" \
      "(a||b||d||e||f||g)&&(a||b||d||e||f||h)&&(a||b||d||e||g||h)&&(a||b||d||f||g||h)&&(a||b||e||f||g||h)&&" \
      "(a||c||d||e||f||g)&&(a||c||d||e||f||h)&&(a||c||d||e||g||h)&&(a||c||d||f||g||h)&&(a||c||e||f||g||h)&&" \
      "(a||d||e||f||g||h)&&(!b||!c||!d||!e)&&(!b||!c||!d||!f)&&(!b||!c||!d||!g)&&(!b||!c||!d||!h)&&" \
      "(!b||!c||!e||!f)&&(!b||!c||!e||!g)&&(!b||!c||!e||!h)&&(!b||!c||!f||!g)&&(!b||!c||!f||!h)&&" \
      "(!b||!c||!g||!h)&&(!b||!d||!e||!f)&&(!b||!d||!e||!g)&&(!b||!d||!e||!h)&&(!b||!d||!f||!g)&&" \
      "(!b||!d||!f||!h)&&(!b||!d||!g||!h)&&(!b||!e||!f||!g)&&(!b||!e||!f||!h)&&(!b||!e||!g||!h)&&" \
      "(!b||!f||!g||!h)&&(b||c||d||e||f||g)&&(b||c||d||e||f||h)&&(b||c||d||e||g||h)&&(b||c||d||f||g||h)&&" \
      "(b||c||e||f||g||h)&&(b||d||e||f||g||h)&&(!c||!d||!e||!f)&&(!c||!d||!e||!g)&&(!c||!d||!e||!h)&&" \
      "(!c||!d||!f||!g)&&(!c||!d||!f||!h)&&(!c||!d||!g||!h)&&(!c||!e||!f||!g)&&(!c||!e||!f||!h)&&" \
      "(!c||!e||!g||!h)&&(!c||!f||!g||!h)&&(c||d||e||f||g||h)&&(!d||!e||!f||!g)&&(!d||!e||!f||!h)&&" \
      "(!d||!e||!g||!h)&&(!d||!f||!g||!h)&&(!e||!f||!g||!h)"
    return mathematica_to_CNF(s, a)

def POPCNT4 (a):
    s="(!a||!b||!c||!d||!e)&&(!a||!b||!c||!d||!f)&&(!a||!b||!c||!d||!g)&&(!a||!b||!c||!d||!h)&&" \
      "(!a||!b||!c||!e||!f)&&(!a||!b||!c||!e||!g)&&(!a||!b||!c||!e||!h)&&(!a||!b||!c||!f||!g)&&" \
      "(!a||!b||!c||!f||!h)&&(!a||!b||!c||!g||!h)&&(!a||!b||!d||!e||!f)&&(!a||!b||!d||!e||!g)&&" \
      "(!a||!b||!d||!e||!h)&&(!a||!b||!d||!f||!g)&&(!a||!b||!d||!f||!h)&&(!a||!b||!d||!g||!h)&&" \
      "(!a||!b||!e||!f||!g)&&(!a||!b||!e||!f||!h)&&(!a||!b||!e||!g||!h)&&(!a||!b||!f||!g||!h)&&" \
      "(!a||!c||!d||!e||!f)&&(!a||!c||!d||!e||!g)&&(!a||!c||!d||!e||!h)&&(!a||!c||!d||!f||!g)&&" \
      "(!a||!c||!d||!f||!h)&&(!a||!c||!d||!g||!h)&&(!a||!c||!e||!f||!g)&&(!a||!c||!e||!f||!h)&&" \
      "(!a||!c||!e||!g||!h)&&(!a||!c||!f||!g||!h)&&(!a||!d||!e||!f||!g)&&(!a||!d||!e||!f||!h)&&" \
      "(!a||!d||!e||!g||!h)&&(!a||!d||!f||!g||!h)&&(!a||!e||!f||!g||!h)&&(a||b||c||d||e)&&(a||b||c||d||f)&&" \
      "(a||b||c||d||g)&&(a||b||c||d||h)&&(a||b||c||e||f)&&(a||b||c||e||g)&&(a||b||c||e||h)&&(a||b||c||f||g)&&" \
      "(a||b||c||f||h)&&(a||b||c||g||h)&&(a||b||d||e||f)&&(a||b||d||e||g)&&(a||b||d||e||h)&&(a||b||d||f||g)&&" \
      "(a||b||d||f||h)&&(a||b||d||g||h)&&(a||b||e||f||g)&&(a||b||e||f||h)&&(a||b||e||g||h)&&(a||b||f||g||h)&&" \
      "(a||c||d||e||f)&&(a||c||d||e||g)&&(a||c||d||e||h)&&(a||c||d||f||g)&&(a||c||d||f||h)&&(a||c||d||g||h)&&" \
      "(a||c||e||f||g)&&(a||c||e||f||h)&&(a||c||e||g||h)&&(a||c||f||g||h)&&(a||d||e||f||g)&&(a||d||e||f||h)&&" \
      "(a||d||e||g||h)&&(a||d||f||g||h)&&(a||e||f||g||h)&&(!b||!c||!d||!e||!f)&&(!b||!c||!d||!e||!g)&&" \
      "(!b||!c||!d||!e||!h)&&(!b||!c||!d||!f||!g)&&(!b||!c||!d||!f||!h)&&(!b||!c||!d||!g||!h)&&" \
      "(!b||!c||!e||!f||!g)&&(!b||!c||!e||!f||!h)&&(!b||!c||!e||!g||!h)&&(!b||!c||!f||!g||!h)&&" \
      "(!b||!d||!e||!f||!g)&&(!b||!d||!e||!f||!h)&&(!b||!d||!e||!g||!h)&&(!b||!d||!f||!g||!h)&&" \
      "(!b||!e||!f||!g||!h)&&(b||c||d||e||f)&&(b||c||d||e||g)&&(b||c||d||e||h)&&(b||c||d||f||g)&&" \
      "(b||c||d||f||h)&&(b||c||d||g||h)&&(b||c||e||f||g)&&(b||c||e||f||h)&&(b||c||e||g||h)&&" \
      "(b||c||f||g||h)&&(b||d||e||f||g)&&(b||d||e||f||h)&&(b||d||e||g||h)&&(b||d||f||g||h)&&" \
      "(b||e||f||g||h)&&(!c||!d||!e||!f||!g)&&(!c||!d||!e||!f||!h)&&(!c||!d||!e||!g||!h)&&" \
      "(!c||!d||!f||!g||!h)&&(!c||!e||!f||!g||!h)&&(c||d||e||f||g)&&(c||d||e||f||h)&&(c||d||e||g||h)&&" \
      "(c||d||f||g||h)&&(c||e||f||g||h)&&(!d||!e||!f||!g||!h)&&(d||e||f||g||h)"
    return mathematica_to_CNF(s, a)

def POPCNT5 (a):
    s="(!a||!b||!c||!d||!e||!f)&&(!a||!b||!c||!d||!e||!g)&&(!a||!b||!c||!d||!e||!h)&&" \
      "(!a||!b||!c||!d||!f||!g)&&(!a||!b||!c||!d||!f||!h)&&(!a||!b||!c||!d||!g||!h)&&" \
      "(!a||!b||!c||!e||!f||!g)&&(!a||!b||!c||!e||!f||!h)&&(!a||!b||!c||!e||!g||!h)&&" \
      "(!a||!b||!c||!f||!g||!h)&&(!a||!b||!d||!e||!f||!g)&&(!a||!b||!d||!e||!f||!h)&&" \
      "(!a||!b||!d||!e||!g||!h)&&(!a||!b||!d||!f||!g||!h)&&(!a||!b||!e||!f||!g||!h)&&" \
      "(!a||!c||!d||!e||!f||!g)&&(!a||!c||!d||!e||!f||!h)&&(!a||!c||!d||!e||!g||!h)&&" \
      "(!a||!c||!d||!f||!g||!h)&&(!a||!c||!e||!f||!g||!h)&&(!a||!d||!e||!f||!g||!h)&&" \
      "(a||b||c||d)&&(a||b||c||e)&&(a||b||c||f)&&(a||b||c||g)&&(a||b||c||h)&&(a||b||d||e)&&" \
      "(a||b||d||f)&&(a||b||d||g)&&(a||b||d||h)&&(a||b||e||f)&&(a||b||e||g)&&(a||b||e||h)&&" \
      "(a||b||f||g)&&(a||b||f||h)&&(a||b||g||h)&&(a||c||d||e)&&(a||c||d||f)&&(a||c||d||g)&&" \
      "(a||c||d||h)&&(a||c||e||f)&&(a||c||e||g)&&(a||c||e||h)&&(a||c||f||g)&&(a||c||f||h)&&" \
      "(a||c||g||h)&&(a||d||e||f)&&(a||d||e||g)&&(a||d||e||h)&&(a||d||f||g)&&(a||d||f||h)&&" \
      "(a||d||g||h)&&(a||e||f||g)&&(a||e||f||h)&&(a||e||g||h)&&(a||f||g||h)&&(!b||!c||!d||!e||!f||!g)&&" \
      "(!b||!c||!d||!e||!f||!h)&&(!b||!c||!d||!e||!g||!h)&&(!b||!c||!d||!f||!g||!h)&&" \
      "(!b||!c||!e||!f||!g||!h)&&(!b||!d||!e||!f||!g||!h)&&(b||c||d||e)&&(b||c||d||f)&&" \
      "(b||c||d||g)&&(b||c||d||h)&&(b||c||e||f)&&(b||c||e||g)&&(b||c||e||h)&&(b||c||f||g)&&" \
      "(b||c||f||h)&&(b||c||g||h)&&(b||d||e||f)&&(b||d||e||g)&&(b||d||e||h)&&(b||d||f||g)&&" \
      "(b||d||f||h)&&(b||d||g||h)&&(b||e||f||g)&&(b||e||f||h)&&(b||e||g||h)&&(b||f||g||h)&&" \
      "(!c||!d||!e||!f||!g||!h)&&(c||d||e||f)&&(c||d||e||g)&&(c||d||e||h)&&(c||d||f||g)&&" \
      "(c||d||f||h)&&(c||d||g||h)&&(c||e||f||g)&&(c||e||f||h)&&(c||e||g||h)&&(c||f||g||h)&&" \
      "(d||e||f||g)&&(d||e||f||h)&&(d||e||g||h)&&(d||f||g||h)&&(e||f||g||h)"
    return mathematica_to_CNF(s, a)

def POPCNT6 (a):
    s="(!a||!b||!c||!d||!e||!f||!g)&&(!a||!b||!c||!d||!e||!f||!h)&&(!a||!b||!c||!d||!e||!g||!h)&&" \
      "(!a||!b||!c||!d||!f||!g||!h)&&(!a||!b||!c||!e||!f||!g||!h)&&(!a||!b||!d||!e||!f||!g||!h)&&" \
      "(!a||!c||!d||!e||!f||!g||!h)&&(a||b||c)&&(a||b||d)&&(a||b||e)&&(a||b||f)&&(a||b||g)&&(a||b||h)&&" \
      "(a||c||d)&&(a||c||e)&&(a||c||f)&&(a||c||g)&&(a||c||h)&&(a||d||e)&&(a||d||f)&&(a||d||g)&&" \
      "(a||d||h)&&(a||e||f)&&(a||e||g)&&(a||e||h)&&(a||f||g)&&(a||f||h)&&(a||g||h)&&" \
      "(!b||!c||!d||!e||!f||!g||!h)&&(b||c||d)&&(b||c||e)&&(b||c||f)&&(b||c||g)&&(b||c||h)&&(b||d||e)&&" \
      "(b||d||f)&&(b||d||g)&&(b||d||h)&&(b||e||f)&&(b||e||g)&&(b||e||h)&&(b||f||g)&&(b||f||h)&&(b||g||h)&&" \
      "(c||d||e)&&(c||d||f)&&(c||d||g)&&(c||d||h)&&(c||e||f)&&(c||e||g)&&(c||e||h)&&(c||f||g)&&(c||f||h)&&" \
      "(c||g||h)&&(d||e||f)&&(d||e||g)&&(d||e||h)&&(d||f||g)&&(d||f||h)&&(d||g||h)&&" \
      "(e||f||g)&&(e||f||h)&&(e||g||h)&&(f||g||h)"
    return mathematica_to_CNF(s, a)

def POPCNT7 (a):
    s="(!a||!b||!c||!d||!e||!f||!g||!h)&&(a||b)&&(a||c)&&(a||d)&&(a||e)&&(a||f)&&(a||g)&&(a||h)&&(b||c)&&" \
      "(b||d)&&(b||e)&&(b||f)&&(b||g)&&(b||h)&&(c||d)&&(c||e)&&(c||f)&&(c||g)&&(c||h)&&(d||e)&&(d||f)&&(d||g)&&" \
      "(d||h)&&(e||f)&&(e||g)&&(e||h)&&(f||g)&&(f||h)&&(g||h)"
    return mathematica_to_CNF(s, a)

def POPCNT8 (a):
    s="a&&b&&c&&d&&e&&f&&g&&h"
    return mathematica_to_CNF(s, a)

POPCNT_functions=[POPCNT0, POPCNT1, POPCNT2, POPCNT3, POPCNT4, POPCNT5, POPCNT6, POPCNT7, POPCNT8]

def coords_to_var (row, col):
    # we always use SAT variables as strings, anyway.
    # the 1st variables is 1, not 0
    return str(row*(WIDTH+2)+col+1)

def chk_bomb(row, col):
    clauses=[]

    # make empty border
    # all variables are negated (because they must be False)
    for c in range(WIDTH+2):
        clauses.append ("-"+coords_to_var(0,c))
        clauses.append ("-"+coords_to_var(HEIGHT+1,c))
    for r in range(HEIGHT+2):
        clauses.append ("-"+coords_to_var(r,0))
        clauses.append ("-"+coords_to_var(r,WIDTH+1))

    for r in range(1,HEIGHT+1):
        for c in range(1,WIDTH+1):
            t=known[r-1][c-1]
            if t in "012345678":
                # cell at r, c is empty (False):
                clauses.append ("-"+coords_to_var(r,c))
                # we need an empty border so the following expression would work for all possible cells:
                neighbours=[coords_to_var(r-1, c-1), coords_to_var(r-1, c), coords_to_var(r-1, c+1), coords_to_var(r, c-1),
                        coords_to_var(r, c+1), coords_to_var(r+1, c-1), coords_to_var(r+1, c), coords_to_var(r+1, c+1)]
                clauses=clauses+POPCNT_functions[int(t)](neighbours)

    # place a bomb
    clauses.append (coords_to_var(row,col))

    f=open("tmp.cnf", "w")
    f.write ("p cnf "+str(VARS_TOTAL)+" "+str(len(clauses))+"\n")
    for c in clauses:
        f.write(c+" 0\n")
    f.close()

    child = subprocess.Popen(["minisat", "tmp.cnf"], stdout=subprocess.PIPE)
    child.wait()
    # 10 is SAT, 20 is UNSAT
    if child.returncode==20:
        print "row=%d, col=%d, unsat!" % (row, col)

for r in range(1,HEIGHT+1):
    for c in range(1,WIDTH+1):
        if known[r-1][c-1]=="?":
            chk_bomb(r, c)

