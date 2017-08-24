#-*- coding: utf-8 -*-

#!/usr/bin/env python

import itertools, subprocess, os

# global variables:
clauses=[]
vector_names={}
last_var=1

BITS_PER_VECTOR=9

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
    [f.write(" ".join(c)+" 0\n") for c in clauses]
    f.close()

def neg(v):
    return "-"+v

def add_popcnt1(vars):
    global clauses
    # enumerate all possible pairs
    # no pair can have both True's
    # so add "~var OR ~var2"
    for pair in itertools.combinations(vars, r=2):
        clauses.append([neg(pair[0]), neg(pair[1])])
    # at least one var must be present:
    clauses.append(vars)

def make_distinct_bits_in_vector(vec_name):
    global vector_names
    global last_var

    add_popcnt1([vector_names[(vec_name,i)] for i in range(BITS_PER_VECTOR)])

def make_distinct_vectors(vectors):
    # take each bit from all vectors, call add_popcnt1()
    for i in range(BITS_PER_VECTOR):
        add_popcnt1([vector_names[(vec,i)] for vec in vectors])

def cvt_vector_to_number(vec_name, solution):
    for i in range(BITS_PER_VECTOR):
        if vector_names[(vec_name,i)] in solution:
            # variable present in solution as non-negated (without a "-" prefix)
            return i+1
    raise AssertionError

def alloc_var():
    global last_var
    last_var=last_var+1
    return str(last_var-1)

def alloc_vector(l, name):
    global last_var
    global vector_names
    rt=[]
    for i in range(l):
        v=alloc_var()
        vector_names[(name,i)]=v
        rt.append(v)
    return rt

def add_constant(var,b):
    global clauses
    if b==True or b==1:
        clauses.append([var])
    else:
        clauses.append([neg(var)])

# vec is a list of True/False/0/1
def add_constant_vector(vec_name, vec):
    global vector_names
    for i in range(BITS_PER_VECTOR):
        add_constant (vector_names[(vec_name, i)], vec[i])

# 1 -> [1, 0, 0, 0, 0, 0, 0, 0, 0]
# 3 -> [0, 0, 1, 0, 0, 0, 0, 0, 0]
def number_to_vector(n):
    rt=[0]*(n-1)
    rt.append(1)
    rt=rt+[0]*(BITS_PER_VECTOR-len(rt))
    return rt

"""
coordinates we're using here:

+--------+--------+--------+
|11 12 13|14 15 16|17 18 19|
|21 22 23|24 25 26|27 28 29|
|31 32 33|34 35 36|37 38 39|
+--------+--------+--------+
|41 42 43|44 45 46|47 48 49|
|51 52 53|54 55 56|57 58 59|
|61 62 63|64 65 66|67 68 69|
+--------+--------+--------+
|71 72 73|74 75 76|77 78 79|
|81 82 83|84 85 86|87 88 89|
|91 92 93|94 95 96|97 98 99|
+--------+--------+--------+
"""
def make_vec_name(row, col):
    return "cell"+str(row)+str(col)

def puzzle_to_clauses (puzzle):
    # process text line:
    current_column=1
    current_row=1
    for i in puzzle:
        if i!='.':
            add_constant_vector(make_vec_name(current_row, current_column), number_to_vector(int(i)))
        current_column=current_column+1
        if current_column==10:
            current_column=1
            current_row=current_row+1

def print_solution(solution):
    for row in range(1,9+1):
        # print row:
        print " ".join([str(cvt_vector_to_number(make_vec_name(row, col), solution)) for col in range(1,9+1)])

def main():
    # allocate 9*9*9=729 variables:
    for row in range(1, 9+1):
        for col in range(1, 9+1):
            alloc_vector(9, make_vec_name(row, col))
            make_distinct_bits_in_vector(make_vec_name(row, col))

    # variables in each row are unique:
    for row in range(1, 9+1):
        make_distinct_vectors([make_vec_name(row, col) for col in range(1, 9+1)])

    # variables in each column are unique:
    for col in range(1, 9+1):
        make_distinct_vectors([make_vec_name(row, col) for row in range(1, 9+1)])

    # variables in each 3*3 box are unique:
    for row in range(1, 9+1, 3):
        for col in range(1, 9+1, 3):
            tmp=[]
            tmp.append(make_vec_name(row+0, col+0))
            tmp.append(make_vec_name(row+0, col+1))
            tmp.append(make_vec_name(row+0, col+2))
            tmp.append(make_vec_name(row+1, col+0))
            tmp.append(make_vec_name(row+1, col+1))
            tmp.append(make_vec_name(row+1, col+2))
            tmp.append(make_vec_name(row+2, col+0))
            tmp.append(make_vec_name(row+2, col+1))
            tmp.append(make_vec_name(row+2, col+2))
            make_distinct_vectors(tmp)

    # http://www.norvig.com/sudoku.html
    # http://www.mirror.co.uk/news/weird-news/worlds-hardest-sudoku-can-you-242294
    puzzle_to_clauses("..53.....8......2..7..1.5..4....53...1..7...6..32...8..6.5....9..4....3......97..")

    print "len(clauses)=",len(clauses)
    write_CNF("1.cnf", clauses, last_var-1)
    solution=run_minisat("1.cnf")
    #os.remove("1.cnf")
    if solution==None:
        print "unsat!"
        exit(0)

    print_solution(solution)

main()

