#-*- coding: utf-8 -*-

#!/usr/bin/env python

import itertools, subprocess, os, frolic, Xu

SIZE=8
SKIP_SYMMETRIES=True
#SKIP_SYMMETRIES=False

def row_col_to_var(row, col):
    global first_var
    return str(row*SIZE+col+first_var)

def gen_diagonal(s, start_row, start_col, increment, limit):
    col=start_col
    tmp=[]
    for row in range(start_row, SIZE):
        tmp.append(row_col_to_var(row, col))
        col=col+increment
        if col==limit:
            break
    # ignore diagonals consisting of 1 cell:
    if len(tmp)>1:
        # we can't use POPCNT1() here, since some diagonals are empty in valid solutions.
        s.AtMost1(tmp)

def add_2D_array_as_negated_constraint(s, a):
    negated_solution=[]
    for row in range(SIZE):
        for col in range(SIZE):
            negated_solution.append(s.neg_if(a[row][col], row_col_to_var(row, col)))
    s.add_clause(negated_solution)

def main():
    global first_var

    s=Xu.Xu(False)

    _vars=s.alloc_BV(SIZE**2)
    first_var=int(_vars[0])

    # enumerate all rows:
    for row in range(SIZE):
        s.POPCNT1([row_col_to_var(row, col) for col in range(SIZE)])

    # enumerate all columns:
    # POPCNT1() could be used here as well:
    for col in range(SIZE):
        s.AtMost1([row_col_to_var(row, col) for row in range(SIZE)])

    # enumerate all diagonals:
    for row in range(SIZE):
        for col in range(SIZE):
            gen_diagonal(s, row, col, 1, SIZE) # from L to R
            gen_diagonal(s, row, col, -1, -1)  # from R to L

    # find all solutions:
    sol_n=1
    while True:
        if s.solve()==False:
            print "unsat!"
            print "solutions total=", sol_n-1
            exit(0)

        # print solution:
        print "solution number", sol_n, ":"

        # get solution and make 2D array of bools:
        solution_as_2D_bool_array=[]
        for row in range(SIZE):
            solution_as_2D_bool_array.append ([s.get_var_from_solution(row_col_to_var(row, col)) for col in range(SIZE)])

        # print 2D array:
        for row in range(SIZE):
            tmp=[([" ", "*"][solution_as_2D_bool_array[row][col]]+"|") for col in range(SIZE)]
            print "|"+"".join(tmp)

        # add 2D array as negated constraint:
        add_2D_array_as_negated_constraint(s, solution_as_2D_bool_array)

        # if we skip symmetries, rotate/reflect soluion and add them as negated constraints:
        if SKIP_SYMMETRIES:
            for a in range(4):
                tmp=frolic.rotate_rect_array(solution_as_2D_bool_array, a)
                add_2D_array_as_negated_constraint(s, tmp)
        
                tmp=frolic.reflect_horizontally(frolic.rotate_rect_array(solution_as_2D_bool_array, a))
                add_2D_array_as_negated_constraint(s, tmp)

        sol_n=sol_n+1

main()

