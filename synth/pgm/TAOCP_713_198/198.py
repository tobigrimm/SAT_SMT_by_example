from z3 import *

a, b, c=BitVecs('a b c', 22)

s=Solver()

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
        s.add(((a >> ((x>>b) & c)) & 3) == (t-1))

# enumerate all solutions:
results=[]
while s.check() == sat:
    m = s.model()

    print "a,b,c = 0x%x 0x%x 0x%x" % (m[a].as_long(), m[b].as_long(), m[c].as_long())

    results.append(m)
    block = []
    for d in m:
        t=d()
        block.append(t != m[d])
    s.add(Or(block))
        
print "results total=", len(results)

