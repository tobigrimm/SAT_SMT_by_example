#!/usr/bin/env python
seed=11223344

def rand():
    global seed
    seed=seed*1103515245+12345
    return (seed>>16) & 0x7fff

for i in range(10):
    print rand()
