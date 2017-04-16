#!/usr/bin/python

import os
from GoL_SAT_utils import *

"""
final_state=[
" * ",
"* *",
" * "]
"""

"""
final_state=[
"***",
"* *",
"***"]
"""

"""
final_state=[
" * ",
" * ",
" * "]
"""

"""
final_state=[
"  *  ",
"     ",
" **  ",
"  *  ",
"  *  ",
" *** "]
"""

"""
final_state=[
"  *  ",
" * * ",
"*   *",
" * * ",
"  *  "]
"""

#"""
final_state=[
"             ",
"   *     *   ",
"    *   *    ",
"   *******   ",
"  ** *** **  ",
" *********** ",
" * ******* * ",
" * *     * * ",
"    ** **    ",
"             "]
#"""

H=len(final_state) # HEIGHT
W=len(final_state[0]) # WIDTH

print "HEIGHT=", H, "WIDTH=", W

VARS_TOTAL=W*H+1
VAR_FALSE=str(VARS_TOTAL)

def try_again (clauses):
    # rules for the main part of grid
    for r in range(H):
        for c in range(W):
            if final_state[r][c]=="*":
                clauses=clauses+cell_is_true(coords_to_var(r, c, H, W), get_neighbours(r, c, H, W))
            else:
                clauses=clauses+cell_is_false(coords_to_var(r, c, H, W), get_neighbours(r, c, H, W))
    
    # cells behind visible grid must always be false:
    for c in range(-1, W+1):
        for r in [-1,H]:
            clauses=clauses+cell_is_false(coords_to_var(r, c, H, W), get_neighbours(r, c, H, W))
    for c in [-1,W]:
        for r in range(-1, H+1):
            clauses=clauses+cell_is_false(coords_to_var(r, c, H, W), get_neighbours(r, c, H, W))

    write_CNF("tmp.cnf", clauses, VARS_TOTAL)

    print "%d clauses" % len(clauses)

    solution=run_minisat ("tmp.cnf")
    os.remove("tmp.cnf")
    if solution==None:
        print "unsat!"
        exit(0)
    
    grid=SAT_solution_to_grid(solution, H, W)

    print_grid(grid)
    write_RLE(grid)

    return grid

clauses=[]
# always false:
clauses.append ("-"+VAR_FALSE)

while True:
    solution=try_again(clauses)
    clauses.append(negate_clause(grid_to_clause(solution, H, W)))
    clauses.append(negate_clause(grid_to_clause(reflect_vertically(solution), H, W)))
    clauses.append(negate_clause(grid_to_clause(reflect_horizontally(solution), H, W)))
    # is this square?
    if W==H:
        clauses.append(negate_clause(grid_to_clause(rotate_square_array(solution,1), H, W)))
        clauses.append(negate_clause(grid_to_clause(rotate_square_array(solution,2), H, W)))
        clauses.append(negate_clause(grid_to_clause(rotate_square_array(solution,3), H, W)))
    print ""

