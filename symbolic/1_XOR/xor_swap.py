#!/usr/bin/env python
class Expr:
    def __init__(self,s):
        self.s=s
    
    def __str__(self):
        return self.s

    def __xor__(self, other):
        return Expr("(" + self.s + "^" + other.s + ")")

def XOR_swap(X, Y):
    X=X^Y
    Y=Y^X
    X=X^Y
    return X, Y

new_X, new_Y=XOR_swap(Expr("X"), Expr("Y"))
print "new_X", new_X
print "new_Y", new_Y

