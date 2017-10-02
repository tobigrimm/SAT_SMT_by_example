#!/usr/bin/env python3

# Python utils

def read_lines_from_file (fname):
    f=open(fname)
    new_ar=[item.rstrip() for item in f.readlines()]
    f.close()
    return new_ar

# reverse list:
def rvr(i):
    return i[::-1]

