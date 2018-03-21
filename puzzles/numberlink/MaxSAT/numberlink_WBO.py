#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, os, itertools
import my_utils, SAT_lib
import random

BITS_PER_CELL=4

puzzle=[" 1 5  3  6",
"         2",
" 5        ",
"          ",
"7         ",
"    3  2  ",
" 4  6     ",
"        8 ",
"   19 7   ",
"4      89 "]

width=len(puzzle[0])
height=len(puzzle)

def do_all():
    #s=SAT_lib.SAT_lib(maxsat=False)
    s=SAT_lib.SAT_lib(maxsat=True)

    cells=[[s.alloc_BV(BITS_PER_CELL) for c in range(width)] for r in range(height)]

    L=[[s.create_var() for c in range(width)] for r in range(height)]
    R=[[s.create_var() for c in range(width)] for r in range(height)]
    U=[[s.create_var() for c in range(width)] for r in range(height)]
    D=[[s.create_var() for c in range(width)] for r in range(height)]

    cell_is_empty=[[s.create_var() for c in range(width)] for r in range(height)]

    # U for a cell must be equal to D of the cell above, etc:
    for r in range(height):
        for c in range(width):
            if r!=0:
                s.fix_EQ(U[r][c], D[r-1][c])
            if r!=height-1:
                s.fix_EQ(D[r][c], U[r+1][c])
            if c!=0:
                s.fix_EQ(L[r][c], R[r][c-1])
            if c!=width-1:
                s.fix_EQ(R[r][c], L[r][c+1])

            # "maximize" number of empty cells:
            s.fix_soft_always_true(cell_is_empty[r][c], 1)

    for r in range(height):
        for c in range(width):
            t=puzzle[r][c]
            if t==' ':
                # puzzle has space, so degree=2, IOW, this cell must have 2 connections, no more, no less.
                # enumerate all possible L/R/U/D booleans. two of them must be True, others are False.
                t=[]
                t.append(s.AND_list([s.NOT(cell_is_empty[r][c]), L[r][c], R[r][c], s.NOT(U[r][c]), s.NOT(D[r][c])]))
                t.append(s.AND_list([s.NOT(cell_is_empty[r][c]), L[r][c], s.NOT(R[r][c]), U[r][c], s.NOT(D[r][c])]))
                t.append(s.AND_list([s.NOT(cell_is_empty[r][c]), L[r][c], s.NOT(R[r][c]), s.NOT(U[r][c]), D[r][c]]))
                t.append(s.AND_list([s.NOT(cell_is_empty[r][c]), s.NOT(L[r][c]), R[r][c], U[r][c], s.NOT(D[r][c])]))
                t.append(s.AND_list([s.NOT(cell_is_empty[r][c]), s.NOT(L[r][c]), R[r][c], s.NOT(U[r][c]), D[r][c]]))
                t.append(s.AND_list([s.NOT(cell_is_empty[r][c]), s.NOT(L[r][c]), s.NOT(R[r][c]), U[r][c], D[r][c]]))
                # OR this cell has degree=0, i.e., no links:
                t.append(s.AND_list([cell_is_empty[r][c], s.NOT(L[r][c]), s.NOT(R[r][c]), s.NOT(U[r][c]), s.NOT(D[r][c])]))
                s.fix_always_true(s.OR_list(t))
            else:
                # cell has number, add it to cells[][] as a constraint:
                s.fix_BV(cells[r][c], SAT_lib.n_to_BV(int(t), BITS_PER_CELL))
                # cell has degree=1, IOW, this cell must have 1 connection, no more, no less
                # enumerate all possible ways:
                t=[]
                t.append(s.AND_list([L[r][c], s.NOT(R[r][c]), s.NOT(U[r][c]), s.NOT(D[r][c])]))
                t.append(s.AND_list([s.NOT(L[r][c]), R[r][c], s.NOT(U[r][c]), s.NOT(D[r][c])]))
                t.append(s.AND_list([s.NOT(L[r][c]), s.NOT(R[r][c]), U[r][c], s.NOT(D[r][c])]))
                t.append(s.AND_list([s.NOT(L[r][c]), s.NOT(R[r][c]), s.NOT(U[r][c]), D[r][c]]))
                s.fix_always_true(s.OR_list(t))
    
            # if L[][]==True, cell's number must be equal to the number of cell at left, etc:
            if c!=0:
                s.fix_always_true(s.ITE(L[r][c], s.const_true, s.BV_EQ(cells[r][c], cells[r][c-1])))
            if c!=width-1:
                s.fix_always_true(s.ITE(R[r][c], s.const_true, s.BV_EQ(cells[r][c], cells[r][c+1])))
            if r!=0:
                s.fix_always_true(s.ITE(U[r][c], s.const_true, s.BV_EQ(cells[r][c], cells[r-1][c])))
            if r!=height-1:
                s.fix_always_true(s.ITE(D[r][c], s.const_true, s.BV_EQ(cells[r][c], cells[r+1][c])))

    # L/R/U/D's of borderline cells must always be False:
    for r in range(height):
        s.fix_always_false(L[r][0])
        s.fix_always_false(R[r][width-1])

    for c in range(width):
        s.fix_always_false(U[0][c])
        s.fix_always_false(D[height-1][c])

    if s.solve()==False:
        print ("unsat")
        exit(0)
    else:
        print ("sat")

    print ("")

    for r in range(height):
        t=""
        for c in range(width):
            t=t+("%2d" % SAT_lib.BV_to_number(s.get_BV_from_solution(cells[r][c])))+" "
        print (t)

    print ("")

    for r in range(height):
        t=""
        for c in range(width):
            t=t+("L" if s.get_var_from_solution(L[r][c]) else " ")
            t=t+("R" if s.get_var_from_solution(R[r][c]) else " ")
            t=t+("U" if s.get_var_from_solution(U[r][c]) else " ")
            t=t+("D" if s.get_var_from_solution(D[r][c]) else " ")
            t=t+"|"
        print (t)
    
    print ("")

    for r in range(height):
        row=""
        for c in range(width):
            t=puzzle[r][c]
            if t==' ':
                tl=(True if s.get_var_from_solution(L[r][c]) else False)
                tr=(True if s.get_var_from_solution(R[r][c]) else False)
                tu=(True if s.get_var_from_solution(U[r][c]) else False)
                td=(True if s.get_var_from_solution(D[r][c]) else False)
    
                if tl==False and tr==False and tu==False and td==False:
                    row=row+" "
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
        print (row)
 
do_all()

