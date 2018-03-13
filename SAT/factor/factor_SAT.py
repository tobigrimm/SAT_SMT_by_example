#!/usr/bin/env python3

import itertools, subprocess, os, math, random
from operator import mul
import my_utils, SAT_lib
import functools

def factor(n):
    print ("factoring %d" % n)

    # size of inputs.
    # in other words, how many bits we have to allocate to store 'n'?
    input_bits=int(math.ceil(math.log(n,2)))
    print ("input_bits=%d" % input_bits)

    s=SAT_lib.SAT_lib(False)

    factor1,factor2=s.alloc_BV(input_bits),s.alloc_BV(input_bits)
    product=s.multiplier(factor1,factor2)

    # at least one bit in each input must be set, except lowest.
    # hence we restrict inputs to be greater than 1
    s.fix(s.OR_list(factor1[:-1]), True)
    s.fix(s.OR_list(factor2[:-1]), True)

    # output has a size twice as bigger as each input:
    s.fix_BV(product, SAT_lib.n_to_BV(n,input_bits*2))

    if s.solve()==False:
        print ("%d is prime (unsat)" % n)
        return [n]

    # get inputs of multiplier:
    factor1_n=SAT_lib.BV_to_number(s.get_BV_from_solution(factor1))
    factor2_n=SAT_lib.BV_to_number(s.get_BV_from_solution(factor2))

    print ("factors of %d are %d and %d" % (n, factor1_n, factor2_n))
    # factor factors recursively:
    rt=sorted(factor (factor1_n) + factor (factor2_n))
    assert functools.reduce(mul, rt, 1)==n
    return rt

# infinite test:
def test():
    while True:
        print (factor (random.randrange(100000000000)))

#test()

print (factor(1234567890))

