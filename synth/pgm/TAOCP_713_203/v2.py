from z3 import *

s=Solver()

a, b, c, d, e=BitVecs('a b c d e', 64)

s.add(a==0x0008000400020001)
#s.add(b==0x0f0f0f0f0f0f0f0f)
#s.add(c==0x0606060606060606)
#s.add(d==0x0000002700000000)
#s.add(e==0x2a2a2a2a2a2a2a2a)

def simulate_MOR(y,z):
    """
    set each bit of 64-bit result, as:

    $x_i_j = y_0_j z_i_0 \vee y_1_j z_i_1 \vee \cdots \vee y_7_j z_i_7$
    https://latexbase.com/d/bf2243f8-5d0b-4231-8891-66fb47d846f0

    IOW:

    x<byte><bit> = (y<0><bit> AND z<byte><0>) OR (y<1><bit> AND z<byte><1>) OR ... OR (y<7><bit> AND z<byte><7>)
    """

    def get_ij(x, i, j):
        return (x>>(i*8+j))&1

    rt=0
    for byte in range(8):
        for bit in range(8):
            t=0
            for i in range(8):
                t|=get_ij(y, i, bit) & get_ij(z, byte, i)

            pos=byte*8+bit
            rt|=t<<pos

    return rt

def simulate_pgm(x):
    t=simulate_MOR(x,a)
    s=t<<4
    t=s^t
    t=t&b
    t=t+c
    s=simulate_MOR(d,t)
    t=t+e
    y=t+s
    return y

def nibble_to_ASCII(x):
    return If(And(x>=0, x<=9), 0x30+x, 0x61+x-10)

def method2(x):
    rt=0
    for i in range(8):
        rt|=nibble_to_ASCII((x >> i*4)&0xf) << i*8
    return rt

#"""
# new version.
# for all possible 32-bit x's, find such a/b/c/d/e, so that these two parts would be equal to each other
# zero extend x to 64-bit value in both cases
x=BitVec('x', 32)
s.add(ForAll([x], simulate_pgm(ZeroExt(32, x))==method2(ZeroExt(32, x))))
#"""

"""
# previously:
for i in range(5):
    x=random.getrandbits(32)
    t="%08x" % x
    y=int(''.join("%02X" % ord(c) for c in t), 16)
    print "%x %x" % (x, y)

    s.add(simulate_pgm(x)==y)
"""

# enumerate all solutions:
results=[]
while s.check() == sat:
    m = s.model()

    print "a,b,c,d,e = %x %x %x %x %x" % (m[a].as_long(), m[b].as_long(), m[c].as_long(), m[d].as_long(), m[e].as_long())

    results.append(m)
    block = []
    for d1 in m:
        t=d1()
        block.append(t != m[d1])
    s.add(Or(block))

print "results total=", len(results)

