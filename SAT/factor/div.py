#!/usr/bin/env python3

import itertools, subprocess, os, math, random
from operator import mul
import frolic, Xu

def div(dividend,divisor):

    # size of inputs.
    # in other words, how many bits we have to allocate to store 'n'?
    input_bits=int(math.ceil(math.log(dividend,2)))
    print ("input_bits=%d" % input_bits)

    s=Xu.Xu(False)

    factor1,factor2=s.alloc_BV(input_bits),s.alloc_BV(input_bits)
    product=s.multiplier(factor1,factor2)

    # connect divisor to one of multiplier's input:
    s.fix_BV(factor1, Xu.n_to_BV(divisor,input_bits))
    # output has a size twice as bigger as each input.
    # connect dividend to multiplier's output:
    s.fix_BV(product, Xu.n_to_BV(dividend,input_bits*2))

    if s.solve()==False:
        print ("remainder!=0 (unsat)")
        return None

    # get 2nd input of multiplier, which is quotient:
    return Xu.BV_to_number(s.get_BV_from_solution(factor2))

print (div (12345678901234567890123456789*12345, 12345))

