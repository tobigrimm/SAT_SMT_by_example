from MK85 import *

s=MK85(verbose=0)

# FIXME: must work with 22-bit bitvecs:
a=s.BitVec('a', 32)
b=s.BitVec('b', 32)
c=s.BitVec('c', 32)

# make a,c more aesthetically appealing:
s.add((a&0xff00ffff)==0)
s.add((c&0xffffff00)==0)

def bytes_in_UTF8_seq(x):
    if (x>>7)==0:
        return 1
    if (x>>5)==0b110:
        return 2
    if (x>>4)==0b1110:
        return 3
    if (x>>3)==0b11110:
        return 4
    # invalid 1st byte
    return None

for x in range(256):
    t=bytes_in_UTF8_seq(x)
    if t!=None:
        #print x, t
        s.add(((a >> ((s.BitVecConst(x, 32)>>b) & c)) & 3) == (t-1))

# enumerate all solutions:
results=[]
while s.check():
    m = s.model()
    print "a,b,c = 0x%x 0x%x 0x%x" % (m["a"], m["b"], m["c"])

    # block current solution and solve again:
    s.add(expr.Not(And(a==m["a"], b==m["b"], c==m["c"])))

print "results total=", len(results)

"""
a,b,c = 0xe50000 0x3 0x96
a,b,c = 0xe50000 0x3 0x56
a,b,c = 0xe50000 0x3 0xd6
a,b,c = 0xe50000 0x3 0x76
a,b,c = 0xe50000 0x3 0xf6

...

"""

