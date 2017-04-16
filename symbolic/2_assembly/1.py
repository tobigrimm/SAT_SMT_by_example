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

    def __xor__(self, other):
        return Expr("(" + self.s + "^" + self.convert_to_Expr_if_int(other).s + ")")
    
    def __and__(self, other):
        return Expr("(" + self.s + "&" + self.convert_to_Expr_if_int(other).s + ")")
    
    def __or__(self, other):
        return Expr("(" + self.s + "|" + self.convert_to_Expr_if_int(other).s + ")")
    
    def __lshift__(self, other):
        return Expr("(" + self.s + "<<" + self.convert_to_Expr_if_int(other).s + ")")
    
    def __rshift__(self, other):
        return Expr("(" + self.s + ">>" + self.convert_to_Expr_if_int(other).s + ")")

# change endianness
ecx=Expr("initial_ECX") # 1st argument
eax=ecx             #  mov     eax, ecx
edx=ecx             #  mov     edx, ecx
edx=edx<<16         #  shl     edx, 16
eax=eax&0xff00      #  and     eax, 0000ff00H
eax=eax|edx         #  or      eax, edx
edx=ecx             #  mov     edx, ecx
edx=edx&0x00ff0000  #  and     edx, 00ff0000H
ecx=ecx>>16         #  shr     ecx, 16
edx=edx|ecx         #  or      edx, ecx
eax=eax<<8          #  shl     eax, 8
edx=edx>>8          #  shr     edx, 8
eax=eax|edx         #  or      eax, edx

print eax

