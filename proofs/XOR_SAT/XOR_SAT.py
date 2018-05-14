#!/usr/bin/env python3

import itertools, subprocess, os, math, random
from operator import mul
import my_utils, SAT_lib

def chk1():
    input_bits=8

    s=SAT_lib.SAT_lib(False)

    x,y=s.alloc_BV(input_bits),s.alloc_BV(input_bits)
    step1=s.BV_AND(x,y)
    minus_2=[s.const_true]*(input_bits-1)+[s.const_false]
    product=s.multiplier(step1,minus_2)[input_bits:]
    result1=s.adder(s.adder(product, x)[0], y)[0]

    result2=s.BV_XOR(x,y)

    s.fix(s.OR_list(s.BV_XOR(result1, result2)), True)

    if s.solve()==False:
        print ("unsat")
        return

    print ("sat")
    print ("x=%x" % SAT_lib.BV_to_number(s.get_BV_from_solution(x)))
    print ("y=%x" % SAT_lib.BV_to_number(s.get_BV_from_solution(y)))
    print ("step1=%x" % SAT_lib.BV_to_number(s.get_BV_from_solution(step1)))
    print ("product=%x" % SAT_lib.BV_to_number(s.get_BV_from_solution(product)))
    print ("result1=%x" % SAT_lib.BV_to_number(s.get_BV_from_solution(result1)))
    print ("result2=%x" % SAT_lib.BV_to_number(s.get_BV_from_solution(result2)))
    print ("minus_2=%x" % SAT_lib.BV_to_number(s.get_BV_from_solution(minus_2)))

def chk2():
    input_bits=64

    s=SAT_lib.SAT_lib(False)

    x,y=s.alloc_BV(input_bits),s.alloc_BV(input_bits)
    step1=s.BV_AND(x,y)
    step2=s.shift_left_1(s.NEG(step1))

    result1=s.adder(s.adder(step2, x)[0], y)[0]

    result2=s.BV_XOR(x,y)

    s.fix(s.OR_list(s.BV_XOR(result1, result2)), True)

    if s.solve()==False:
        print ("unsat")
        return

    print ("sat")
    print ("x=%x" % SAT_lib.BV_to_number(s.get_BV_from_solution(x)))
    print ("y=%x" % SAT_lib.BV_to_number(s.get_BV_from_solution(y)))
    print ("step1=%x" % SAT_lib.BV_to_number(s.get_BV_from_solution(step1)))
    print ("step2=%x" % SAT_lib.BV_to_number(s.get_BV_from_solution(step2)))
    print ("result1=%x" % SAT_lib.BV_to_number(s.get_BV_from_solution(result1)))
    print ("result2=%x" % SAT_lib.BV_to_number(s.get_BV_from_solution(result2)))

#chk1()
chk2()

