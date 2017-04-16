#!/usr/bin/env python
from cmath import exp,pi

def FFT(X):
    n = len(X)
    w = exp(-2*pi*1j/n)
    if n > 1:
        X = FFT(X[::2]) + FFT(X[1::2])
        for k in xrange(n/2):
            xk = X[k]
            X[k] = xk + w**k*X[k+n/2]
            X[k+n/2] = xk - w**k*X[k+n/2]
    return X

print FFT([1,2,3,4,5,6,7,8])

