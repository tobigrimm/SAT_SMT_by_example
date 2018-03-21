#!/usr/bin/env python
# -*- coding: utf-8 -*-

from z3 import *

puzzle=["   4   ",
" 3  25 ",
"   31  ",
"   5   ",
"       ",
"  1    ",
"2   4  "]

width=len(puzzle[0])
height=len(puzzle)

# number for each cell:
cells=[[Int('cell_r%d_c%d' % (r,c)) for c in range(width)] for r in range(height)]

# connections between cells. L means the cell has connection with cell at left, etc:
L=[[Bool('L_r%d_c%d' % (r,c)) for c in range(width)] for r in range(height)]
R=[[Bool('R_r%d_c%d' % (r,c)) for c in range(width)] for r in range(height)]
U=[[Bool('U_r%d_c%d' % (r,c)) for c in range(width)] for r in range(height)]
D=[[Bool('D_r%d_c%d' % (r,c)) for c in range(width)] for r in range(height)]

s=Solver()

# U for a cell must be equal to D of the cell above, etc:
for r in range(height):
    for c in range(width):
        if r!=0:
            s.add(U[r][c]==D[r-1][c])
        if r!=height-1:
            s.add(D[r][c]==U[r+1][c])
        if c!=0:
            s.add(L[r][c]==R[r][c-1])
        if c!=width-1:
            s.add(R[r][c]==L[r][c+1])

# yes, I know, we have 4 bools for each cell at this point, and we can half this number,
# but anyway, for the sake of simplicity, this could be better.

for r in range(height):
    for c in range(width):
        t=puzzle[r][c]
        if t==' ':
            # puzzle has space, so degree=2, IOW, this cell must have 2 connections, no more, no less.
            # enumerate all possible L/R/U/D booleans. two of them must be True, others are False.
            t=[]
            t.append(And(L[r][c], R[r][c], Not(U[r][c]), Not(D[r][c])))
            t.append(And(L[r][c], Not(R[r][c]), U[r][c], Not(D[r][c])))
            t.append(And(L[r][c], Not(R[r][c]), Not(U[r][c]), D[r][c]))
            t.append(And(Not(L[r][c]), R[r][c], U[r][c], Not(D[r][c])))
            t.append(And(Not(L[r][c]), R[r][c], Not(U[r][c]), D[r][c]))
            t.append(And(Not(L[r][c]), Not(R[r][c]), U[r][c], D[r][c]))
            s.add(Or(*t))
        else:
            # puzzle has number, add it to cells[][] as a constraint:
            s.add(cells[r][c]==int(t))
            # cell has degree=1, IOW, this cell must have 1 connection, no more, no less
            # enumerate all possible ways:
            t=[]
            t.append(And(L[r][c], Not(R[r][c]), Not(U[r][c]), Not(D[r][c])))
            t.append(And(Not(L[r][c]), R[r][c], Not(U[r][c]), Not(D[r][c])))
            t.append(And(Not(L[r][c]), Not(R[r][c]), U[r][c], Not(D[r][c])))
            t.append(And(Not(L[r][c]), Not(R[r][c]), Not(U[r][c]), D[r][c]))
            s.add(Or(*t))

        # if L[][]==True, cell's number must be equal to the number of cell at left, etc:
        if c!=0:
            s.add(If(L[r][c], cells[r][c]==cells[r][c-1], True))
        if c!=width-1:
            s.add(If(R[r][c], cells[r][c]==cells[r][c+1], True))
        if r!=0:
            s.add(If(U[r][c], cells[r][c]==cells[r-1][c], True))
        if r!=height-1:
            s.add(If(D[r][c], cells[r][c]==cells[r+1][c], True))

# L/R/U/D at borders sometimes must be always False:
for r in range(height):
    s.add(L[r][0]==False)
    s.add(R[r][width-1]==False)

for c in range(width):
    s.add(U[0][c]==False)
    s.add(D[height-1][c]==False)

# print solution:

print s.check()
m=s.model()

print ""

for r in range(height):
    for c in range(width):
        print m[cells[r][c]],
    print ""

print ""

for r in range(height):
    for c in range(width):
        t=""
        t=t+("L" if str(m[L[r][c]])=="True" else " ")
        t=t+("R" if str(m[R[r][c]])=="True" else " ")
        t=t+("U" if str(m[U[r][c]])=="True" else " ")
        t=t+("D" if str(m[D[r][c]])=="True" else " ")
        print t+"|",
    print ""

print ""

for r in range(height):
    row=""
    for c in range(width):
        t=puzzle[r][c]
        if t==' ':
            tl=(True if str(m[L[r][c]])=="True" else False)
            tr=(True if str(m[R[r][c]])=="True" else False)
            tu=(True if str(m[U[r][c]])=="True" else False)
            td=(True if str(m[D[r][c]])=="True" else False)

            if tu and td:
                row=row+"┃"
            if tr and td:
                row=row+"┏"
            if tr and tu:
                row=row+"┗"
            if tl and td:
                row=row+"┓"
            if tl and tu:
                row=row+"┛"
            if tl and tr:
                row=row+"━"
        else:
            row=row+t
    print row

