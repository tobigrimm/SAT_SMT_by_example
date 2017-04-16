#!/usr/bin/env python
from cmath import exp,pi

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

    def __add__(self, other):
        return Expr("(" + self.s + "+" + self.convert_to_Expr_if_int(other).s + ")")
    
    def __sub__(self, other):
        return Expr("(" + self.s + "-" + self.convert_to_Expr_if_int(other).s + ")")
    
    def __mul__(self, other):
        op1=self.s
        op2=self.convert_to_Expr_if_int(other).s 
        
        if op1=="1":
            return Expr(op2)
        if op2=="1":
            return Expr(op1)

        return Expr("(" + op1 + "*" + op2 + ")")

    def __pow__(self, other):
        op2=self.convert_to_Expr_if_int(other).s
        if op2=="0":
            return Expr("1")
        if op2=="1":
            return Expr(self.s)

        return Expr("(" + self.s + "**" + op2 + ")")
    
def FFT(X):
    n = len(X)
    # cast complex value to string, and then to Expr
    w = Expr(str(exp(-2*pi*1j/n)))
    if n > 1:
        X = FFT(X[::2]) + FFT(X[1::2])
        for k in xrange(n/2):
            xk = X[k]
            X[k] = xk + w**k*X[k+n/2]
            X[k+n/2] = xk - w**k*X[k+n/2]
    return X

input=[Expr("input_%d" % i) for i in range(8)]
output=FFT(input)
for i in range(len(output)):
    print i, ":", output[i]

