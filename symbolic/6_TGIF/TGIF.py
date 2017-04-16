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

    def __div__(self, other):
        return Expr("(" + self.s + "/" + self.convert_to_Expr_if_int(other).s + ")")
    
    def __mod__(self, other):
        return Expr("(" + self.s + "%" + self.convert_to_Expr_if_int(other).s + ")")
    
    def __add__(self, other):
        return Expr("(" + self.s + "+" + self.convert_to_Expr_if_int(other).s + ")")

input=Expr("input")
SECS_DAY=24*60*60
dayno = input / SECS_DAY
wday = (dayno + 4) % 7
print wday
if wday==5:
    print "Thanks God, it's Friday!"

