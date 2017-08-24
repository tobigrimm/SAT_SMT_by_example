#-*- coding: utf-8 -*-

#!/usr/bin/env python

import itertools, subprocess, os

# global variable:
clauses=set()
SIZE=8

def read_lines_from_file (fname):
    f=open(fname)
    new_ar=[item.rstrip() for item in f.readlines()]
    f.close()
    return new_ar

def run_minisat (CNF_fname):
    child = subprocess.Popen(["minisat", CNF_fname, "results.txt"], stdout=subprocess.PIPE)
    child.wait()
    # 10 is SAT, 20 is UNSAT
    if child.returncode==20:
        os.remove ("results.txt")
        return None

    if child.returncode!=10:
        print "(minisat) unknown retcode: ", child.returncode
        exit(0)

    solution=read_lines_from_file("results.txt")[1].split(" ")
    os.remove ("results.txt")

    return solution

def write_CNF(fname, clauses, VARS_TOTAL):
    f=open(fname, "w")
    f.write ("p cnf "+str(VARS_TOTAL)+" "+str(len(clauses))+"\n")
    [f.write(c+" 0\n") for c in clauses]
    f.close()

def neg(v):
    return "-"+v

def add_popcnt0_or_1(vars):
    global clauses
    # enumerate all possible pairs
    # no pair can have both True's
    # so add "~var OR ~var2"
    for pair in itertools.combinations(vars, r=2):
        clauses.add(neg(pair[0])+" "+neg(pair[1]))

def add_popcnt1(vars):
    global clauses
    add_popcnt0_or_1(vars)
    # at least one var must be present:
    clauses.add(" ".join(vars))

def row_col_to_var(row, col):
    return str(row*SIZE+col+1)

def gen_diagonal(start_row, start_col, increment, limit):
    col=start_col
    tmp=[]
    for row in range(start_row, SIZE):
        tmp.append(row_col_to_var(row, col))
        col=col+increment
        if col==limit:
            break
    # ignore diagonals consisting of 1 cell:
    if len(tmp)>1:
        add_popcnt0_or_1(tmp)
    # we can't use add_popcnt1() here, since some diagonals are empty in valid solutions.

def main():
    # enumerate all rows:
    for row in range(SIZE):
        add_popcnt1([row_col_to_var(row, col) for col in range(SIZE)])

    # enumerate all columns:
    # add_popcnt1() could be used here as well:
    for col in range(SIZE):
        add_popcnt0_or_1([row_col_to_var(row, col) for row in range(SIZE)])

    # enumerate all diagonals:
    for row in range(SIZE):
        for col in range(SIZE):
            gen_diagonal(row, col, 1, SIZE) # from L to R
            gen_diagonal(row, col, -1, -1)  # from R to L

    print "len(clauses)=",len(clauses)
    write_CNF("1.cnf", clauses, SIZE*SIZE)
    solution=run_minisat("1.cnf")
    #os.remove("1.cnf")
    if solution==None:
        print "unsat!"
        exit(0)

    # print solution:
    for row in range(SIZE):
        # enumerate all row/columns
        # if corresponding variable present in solution as is (non negated), then print asterisk, or space otherwise:
        print "|"+"".join([[" ", "*"][row_col_to_var(row, col) in solution]+"|" for col in range(SIZE)])

main()

