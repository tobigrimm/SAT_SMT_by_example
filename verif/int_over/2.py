from z3 import *

def func(a):
    return a*1024

a32, out32 = BitVecs('a32 out32', 32)
out32_extended = BitVec('out32_extended', 64)
a64, out64 = BitVecs('a64 out64', 64)

#s=Solver()
s=Optimize()

s.add(out32==func(a32))
s.add(out64==func(a64))

s.add(a64==SignExt(32, a32))
s.add(out32_extended==SignExt(32, out32))
s.add(out64!=out32_extended)

s.minimize(a32)

if s.check()==unsat:
    print "unsat: everything is OK"
    exit(0)
m=s.model()

# from https://stackoverflow.com/questions/1375897/how-to-get-the-signed-integer-value-of-a-long-in-python
def toSigned32(n):
    n = n & 0xffffffff
    return n | (-(n & 0x80000000))

def toSigned64(n):
    n = n & 0xffffffffffffffff
    return n | (-(n & 0x8000000000000000))

print "a32=0x%x or %d" % (m[a32].as_long(), toSigned32(m[a32].as_long()))
print "out32=0x%x or %d" % (m[out32].as_long(), toSigned32(m[out32].as_long()))

print "out32_extended=0x%x or %d" % (m[out32_extended].as_long(), toSigned64(m[out32_extended].as_long()))

print "a64=0x%x or %d" % (m[a64].as_long(), toSigned64(m[a64].as_long()))
print "out64=0x%x or %d" % (m[out64].as_long(), toSigned64(m[out64].as_long()))

