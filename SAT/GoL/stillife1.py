#!/usr/bin/python

import os
from GoL_SAT_utils import *

W=3 # WIDTH
H=3 # HEIGHT

VARS_TOTAL=W*H+1
VAR_FALSE=str(VARS_TOTAL)

def stillife (center, a):
    s="(!a||!b||!c||!center||!d)&&(!a||!b||!c||!center||!e)&&(!a||!b||!c||!center||!f)&&" \
      "(!a||!b||!c||!center||!g)&&(!a||!b||!c||!center||!h)&&(!a||!b||!c||center||d||e||f||g||h)&&" \
      "(!a||!b||c||center||!d||e||f||g||h)&&(!a||!b||c||center||d||!e||f||g||h)&&" \
      "(!a||!b||c||center||d||e||!f||g||h)&&(!a||!b||c||center||d||e||f||!g||h)&&" \
      "(!a||!b||c||center||d||e||f||g||!h)&&(!a||!b||!center||!d||!e)&&(!a||!b||!center||!d||!f)&&" \
      "(!a||!b||!center||!d||!g)&&(!a||!b||!center||!d||!h)&&(!a||!b||!center||!e||!f)&&" \
      "(!a||!b||!center||!e||!g)&&(!a||!b||!center||!e||!h)&&(!a||!b||!center||!f||!g)&&" \
      "(!a||!b||!center||!f||!h)&&(!a||!b||!center||!g||!h)&&(!a||b||!c||center||!d||e||f||g||h)&&" \
      "(!a||b||!c||center||d||!e||f||g||h)&&(!a||b||!c||center||d||e||!f||g||h)&&" \
      "(!a||b||!c||center||d||e||f||!g||h)&&(!a||b||!c||center||d||e||f||g||!h)&&" \
      "(!a||b||c||center||!d||!e||f||g||h)&&(!a||b||c||center||!d||e||!f||g||h)&&" \
      "(!a||b||c||center||!d||e||f||!g||h)&&(!a||b||c||center||!d||e||f||g||!h)&&" \
      "(!a||b||c||center||d||!e||!f||g||h)&&(!a||b||c||center||d||!e||f||!g||h)&&" \
      "(!a||b||c||center||d||!e||f||g||!h)&&(!a||b||c||center||d||e||!f||!g||h)&&" \
      "(!a||b||c||center||d||e||!f||g||!h)&&(!a||b||c||center||d||e||f||!g||!h)&&" \
      "(!a||!c||!center||!d||!e)&&(!a||!c||!center||!d||!f)&&(!a||!c||!center||!d||!g)&&" \
      "(!a||!c||!center||!d||!h)&&(!a||!c||!center||!e||!f)&&(!a||!c||!center||!e||!g)&&" \
      "(!a||!c||!center||!e||!h)&&(!a||!c||!center||!f||!g)&&(!a||!c||!center||!f||!h)&&" \
      "(!a||!c||!center||!g||!h)&&(!a||!center||!d||!e||!f)&&(!a||!center||!d||!e||!g)&&" \
      "(!a||!center||!d||!e||!h)&&(!a||!center||!d||!f||!g)&&(!a||!center||!d||!f||!h)&&" \
      "(!a||!center||!d||!g||!h)&&(!a||!center||!e||!f||!g)&&(!a||!center||!e||!f||!h)&&" \
      "(!a||!center||!e||!g||!h)&&(!a||!center||!f||!g||!h)&&(a||!b||!c||center||!d||e||f||g||h)&&" \
      "(a||!b||!c||center||d||!e||f||g||h)&&(a||!b||!c||center||d||e||!f||g||h)&&" \
      "(a||!b||!c||center||d||e||f||!g||h)&&(a||!b||!c||center||d||e||f||g||!h)&&" \
      "(a||!b||c||center||!d||!e||f||g||h)&&(a||!b||c||center||!d||e||!f||g||h)&&" \
      "(a||!b||c||center||!d||e||f||!g||h)&&(a||!b||c||center||!d||e||f||g||!h)&&" \
      "(a||!b||c||center||d||!e||!f||g||h)&&(a||!b||c||center||d||!e||f||!g||h)&&" \
      "(a||!b||c||center||d||!e||f||g||!h)&&(a||!b||c||center||d||e||!f||!g||h)&&" \
      "(a||!b||c||center||d||e||!f||g||!h)&&(a||!b||c||center||d||e||f||!g||!h)&&" \
      "(a||b||!c||center||!d||!e||f||g||h)&&(a||b||!c||center||!d||e||!f||g||h)&&" \
      "(a||b||!c||center||!d||e||f||!g||h)&&(a||b||!c||center||!d||e||f||g||!h)&&" \
      "(a||b||!c||center||d||!e||!f||g||h)&&(a||b||!c||center||d||!e||f||!g||h)&&" \
      "(a||b||!c||center||d||!e||f||g||!h)&&(a||b||!c||center||d||e||!f||!g||h)&&" \
      "(a||b||!c||center||d||e||!f||g||!h)&&(a||b||!c||center||d||e||f||!g||!h)&&" \
      "(a||b||c||!center||d||e||f||g)&&(a||b||c||!center||d||e||f||h)&&" \
      "(a||b||c||!center||d||e||g||h)&&(a||b||c||!center||d||f||g||h)&&" \
      "(a||b||c||!center||e||f||g||h)&&(a||b||c||center||!d||!e||!f||g||h)&&" \
      "(a||b||c||center||!d||!e||f||!g||h)&&(a||b||c||center||!d||!e||f||g||!h)&&" \
      "(a||b||c||center||!d||e||!f||!g||h)&&(a||b||c||center||!d||e||!f||g||!h)&&" \
      "(a||b||c||center||!d||e||f||!g||!h)&&(a||b||c||center||d||!e||!f||!g||h)&&" \
      "(a||b||c||center||d||!e||!f||g||!h)&&(a||b||c||center||d||!e||f||!g||!h)&&" \
      "(a||b||c||center||d||e||!f||!g||!h)&&(a||b||!center||d||e||f||g||h)&&" \
      "(a||c||!center||d||e||f||g||h)&&(!b||!c||!center||!d||!e)&&(!b||!c||!center||!d||!f)&&" \
      "(!b||!c||!center||!d||!g)&&(!b||!c||!center||!d||!h)&&(!b||!c||!center||!e||!f)&&" \
      "(!b||!c||!center||!e||!g)&&(!b||!c||!center||!e||!h)&&(!b||!c||!center||!f||!g)&&" \
      "(!b||!c||!center||!f||!h)&&(!b||!c||!center||!g||!h)&&(!b||!center||!d||!e||!f)&&" \
      "(!b||!center||!d||!e||!g)&&(!b||!center||!d||!e||!h)&&(!b||!center||!d||!f||!g)&&" \
      "(!b||!center||!d||!f||!h)&&(!b||!center||!d||!g||!h)&&(!b||!center||!e||!f||!g)&&" \
      "(!b||!center||!e||!f||!h)&&(!b||!center||!e||!g||!h)&&(!b||!center||!f||!g||!h)&&" \
      "(b||c||!center||d||e||f||g||h)&&(!c||!center||!d||!e||!f)&&(!c||!center||!d||!e||!g)&&" \
      "(!c||!center||!d||!e||!h)&&(!c||!center||!d||!f||!g)&&(!c||!center||!d||!f||!h)&&" \
      "(!c||!center||!d||!g||!h)&&(!c||!center||!e||!f||!g)&&(!c||!center||!e||!f||!h)&&" \
      "(!c||!center||!e||!g||!h)&&(!c||!center||!f||!g||!h)&&(!center||!d||!e||!f||!g)&&" \
      "(!center||!d||!e||!f||!h)&&(!center||!d||!e||!g||!h)&&(!center||!d||!f||!g||!h)&&" \
      "(!center||!e||!f||!g||!h)"

    return mathematica_to_CNF(s, center, a)

def try_again (clauses):
    # rules for the main part of grid
    for r in range(H):
        for c in range(W):
            clauses=clauses+stillife(coords_to_var(r, c, H, W), get_neighbours(r, c, H, W))
   
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

