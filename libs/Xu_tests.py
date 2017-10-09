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

div_test()

