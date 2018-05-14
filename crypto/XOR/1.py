import sys, hexdump
from z3 import *

def xor_strings(s,t):
    # https://en.wikipedia.org/wiki/XOR_cipher#Example_implementation
    """xor two strings together"""
    return "".join(chr(ord(a)^ord(b)) for a,b in zip(s,t))

def read_file(fname):
    file=open(fname, mode='rb')
    content=file.read()
    file.close()
    return content

def chunks(l, n):
    """divide input buffer by n-len chunks"""
    n = max(1, n)
    return [l[i:i + n] for i in range(0, len(l), n)]

def print_model(m, KEY_LEN, key):
    # fetch key from model:
    test_key="".join(chr(int(obj_to_string(m[key[i]]))) for i in range(KEY_LEN))
    print "key="
    hexdump.hexdump(test_key)

    # decrypt using the key:
    tmp=chunks(cipher_file, KEY_LEN)
    plain_attempt="".join(map(lambda x: xor_strings(x, test_key), tmp))
    print "plain="
    hexdump.hexdump(plain_attempt)

def try_len(KEY_LEN, cipher_file):
    cipher_len=len(cipher_file)
    print "len=", KEY_LEN
    s=Optimize()

    # variables for each byte of key:
    key=[BitVec('key_%d' % i, 8) for i in range (KEY_LEN)]
    # variables for each byte of input cipher text:
    cipher=[BitVec('cipher_%d' % i, 8) for i in range (cipher_len)]
    # variables for each byte of input plain text:
    plain=[BitVec('plain_%d' % i, 8) for i in range (cipher_len)]
    # variable for each byte of plain text: 1 if the byte in 'a'...'z' range:
    az_in_plain=[Int('az_in_plain_%d' % i) for i in range (cipher_len)]

    for i in range(cipher_len):
        # assign each byte of cipher text from the input file:
        s.add(cipher[i]==ord(cipher_file[i]))
        # plain text is cipher text XOR-ed with key:
        s.add(plain[i]==cipher[i]^key[i % KEY_LEN])
        # each byte must be in printable range, or CR of LF:
        s.add(Or(And(plain[i]>=0x20, plain[i]<=0x7E),plain[i]==0xA,plain[i]==0xD))
        # 1 if in 'a'...'z' range, 0 otherwise:
        s.add(az_in_plain[i]==If(And(plain[i]>=ord('a'),plain[i]<=ord('z')), 1, 0))
   
    # find solution, where the sum of all az_in_plain variables is maximum:
    s.maximize(Sum(*az_in_plain))
    
    if s.check()==unsat:
        return
    m=s.model()
    print_model(m, KEY_LEN, key)

cipher_file=read_file (sys.argv[1])

for i in range(1,20):
    try_len(i, cipher_file)

#try_len(17, cipher_file)

