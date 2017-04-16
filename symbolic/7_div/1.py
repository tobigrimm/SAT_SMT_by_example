#!/usr/bin/env python
class Expr:
    def __init__(self,s):
        self.s=s
    
    def convert_to_Expr_if_int(self, n):
        if isinstance(n, int):
            return Expr(str(n))
        if isinstance(n, Expr):
            return n
        raise AssertionError # unsupported type

    def __str__(self):
        return self.s

    def __mul__(self, other):
        return Expr("(" + self.s + "*" + self.convert_to_Expr_if_int(other).s + ")")
    
    def __div__(self, other):
        op2=self.convert_to_Expr_if_int(other).s
        print "warning: division by zero if "+op2+"==0"
        return Expr("(" + self.s + "/" + op2 + ")")
    
    def __add__(self, other):
        return Expr("(" + self.s + "+" + self.convert_to_Expr_if_int(other).s + ")")
    
    def __sub__(self, other):
        return Expr("(" + self.s + "-" + self.convert_to_Expr_if_int(other).s + ")")

"""
     x
------------
2y + 4z - 12

"""

def f(x, y, z):
    return x/(y*2 + z*4 - 12)

print f(Expr("x"), Expr("y"), Expr("z"))

