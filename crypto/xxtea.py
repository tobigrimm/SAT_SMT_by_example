#!/usr/bin/env python

class Expr:
    def __init__(self,s):
        self.s=s
    
    def __str__(self):
        return self.s

    def convert_to_Expr_if_int(self, n):
        if isinstance(n, int):
            return Expr(str(n))
        if isinstance(n, Expr):
            return n
        raise AssertionError # unsupported type

    def __xor__(self, other):
        return Expr("(" + self.s + "^" + self.convert_to_Expr_if_int(other).s + ")")
    
    def __mul__(self, other):
        return Expr("(" + self.s + "*" + self.convert_to_Expr_if_int(other).s + ")")
    
    def __add__(self, other):
        return Expr("(" + self.s + "+" + self.convert_to_Expr_if_int(other).s + ")")

    def __and__(self, other):
        return Expr("(" + self.s + "&" + self.convert_to_Expr_if_int(other).s + ")")
    
    def __lshift__(self, other):
        return Expr("(" + self.s + "<<" + self.convert_to_Expr_if_int(other).s + ")")
    
    def __rshift__(self, other):
        return Expr("(" + self.s + ">>" + self.convert_to_Expr_if_int(other).s + ")")
    
    def __getitem__(self, d):
        return Expr("(" + self.s + "[" + d.s + "])")

# reworked from:

# Pure Python (2.x) implementation of the XXTEA cipher
# (c) 2009. Ivan Voras <ivoras@gmail.com>
# Released under the BSD License.

def raw_xxtea(v, n, k):

    def MX():
        return ((z>>5)^(y<<2)) + ((y>>3)^(z<<4))^(sum^y) + (k[(Expr(str(p)) & 3)^e]^z)

    y = v[0]
    sum = Expr("0")
    DELTA = 0x9e3779b9
    # Encoding only
    z = v[n-1]
    
    # number of rounds:
    #q = 6 + 52 / n
    q=1
    
    while q > 0:
        q -= 1
        sum = sum + DELTA
        e = (sum >> 2) & 3
        p = 0
        while p < n - 1:
            y = v[p+1]
            z = v[p] = v[p] + MX()
            p += 1
        y = v[0]
        z = v[n-1] = v[n-1] + MX()
    return 0

v=[Expr("input1"), Expr("input2"), Expr("input3"), Expr("input4")]
k=Expr("key")

raw_xxtea(v, 4, k)

for i in range(4):
    print i, ":", v[i]
#print len(str(v[0]))+len(str(v[1]))+len(str(v[2]))+len(str(v[3]))

