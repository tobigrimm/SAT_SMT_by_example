#!/usr/bin/env python3

# dennis(a)yurichev, 2017

import frolic, Xu

def div_test():
    s=Xu.Xu(False)

    BITS=32
    divident=s.alloc_BV(BITS)
    divisor=s.alloc_BV(BITS)
    
    s.fix_BV(divident, Xu.n_to_BV(1234567890, BITS))
    s.fix_BV(divisor, Xu.n_to_BV(123, BITS))

    quotient, remainder=s.divider(divident, divisor)

    assert s.solve()==True

    assert Xu.BV_to_number(s.get_BV_from_solution(quotient))==10037137
    assert Xu.BV_to_number(s.get_BV_from_solution(remainder))==39

def SumIsNot1_test():
    s=Xu.Xu(False)

    _vars=s.alloc_BV(4)
    s.SumIsNot1(_vars)

    assert s.count_solutions()==12

def AND_list_test():
    s=Xu.Xu(False)

    _vars=s.alloc_BV(4)
    s.fix(s.AND_list(_vars),False)

    assert (s.count_solutions()==15)

div_test()
SumIsNot1_test()
AND_list_test()

