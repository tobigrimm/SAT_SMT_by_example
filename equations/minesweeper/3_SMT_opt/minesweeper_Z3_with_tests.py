#!/usr/bin/python

from z3 import *
import sys

def find_safe_cells(known):

    WIDTH=len(known[0])
    HEIGHT=len(known)

    def chk_bomb(row, col):

        s=Solver()

        cells=[[Int('r%d_c%d' % (r,c)) for c in range(WIDTH+2)] for r in range(HEIGHT+2)]

        # make border
        for c in range(WIDTH+2):
            s.add(cells[0][c]==0)
            s.add(cells[HEIGHT+1][c]==0)
        for r in range(HEIGHT+2):
            s.add(cells[r][0]==0)
            s.add(cells[r][WIDTH+1]==0)

        for r in range(1,HEIGHT+1):
            for c in range(1,WIDTH+1):

                t=known[r-1][c-1]
                if t in "012345678":
                    s.add(cells[r][c]==0)
                    # we need empty border so the following expression would be able to work for all possible cases:
                    expr=cells[r-1][c-1] + cells[r-1][c] + cells[r-1][c+1] + cells[r][c-1] + cells[r][c+1] + cells[r+1][c-1] + cells[r+1][c] + cells[r+1][c+1]==int(t)
                    if False:
                        print expr
                    s.add(expr)

        # place bomb:
        s.add(cells[row][col]==1)

        if s.check()==unsat:
            return (row, col)
        else:
            return None

    def get_from_known_or_empty(known, r, c):
        # I'm lazy to do overflow checks
        try:
            return known[r][c]
        except IndexError:
            return ""

    def have_neighbour_digit(known, r, c):
        # returns True if neighbour is digit, False otherwise
        digits="0123456789"
        t=[]
        t.append(get_from_known_or_empty(known, r-1, c-1) in digits)
        t.append(get_from_known_or_empty(known, r-1, c) in digits)
        t.append(get_from_known_or_empty(known, r-1, c+1) in digits)
        t.append(get_from_known_or_empty(known, r, c-1) in digits)
        t.append(get_from_known_or_empty(known, r, c+1) in digits)
        t.append(get_from_known_or_empty(known, r+1, c-1) in digits)
        t.append(get_from_known_or_empty(known, r+1, c) in digits)
        t.append(get_from_known_or_empty(known, r+1, c+1) in digits)
        return any(t)

    # enumerate all hidden cells:
    rt=[]
    for r in range(1,HEIGHT+1):
        for c in range(1,WIDTH+1):
            if known[r-1][c-1]=="?" and have_neighbour_digit(known, r-1, c-1):
                #print "checking", r, c
                rt.append(chk_bomb(r, c))
    return filter(None, rt)

tests=[
([
"01?10001?",
"01?100011",
"011100000",
"000000000",
"111110011",
"????1001?",
"????3101?",
"?????211?",
"?????????"],
[(1, 3), (6, 2), (6, 3), (7, 4), (7, 9), (8, 9)]),

([
"01110001?",
"01?100011",
"011100000",
"000000000",
"111110011",
"?11?1001?",
"???331011",
"?????2110",
"???????10"],
[(7, 1), (9, 5), (9, 6)]),

([
"01110001?",
"01?100011",
"011100000",
"000000000",
"111110011",
"?11?1001?",
"222331011",
"??2??2110",
"????22?10"],
[(8, 2), (9, 4)]),

([
"01110001?",
"01?100011",
"011100000",
"000000000",
"111110011",
"?11?1001?",
"222331011",
"?22??2110",
"???322?10"],
[(9, 1), (9, 2)]),
]

for test in tests:
    print "test=", test
    safe_cells=find_safe_cells(test[0])
    print "safe_cells=", safe_cells
    assert test[1]==safe_cells

