"""Universal assignment candidates for bounded-degree nonlinear physical chart images."""
from itertools import combinations
from functools import reduce
from operator import xor
from math import comb
from fixed_height import prior

def assignments(n,a,cap,j):
    if min(n,a,cap,j)<0: raise ValueError('negative parameter')
    weight=min(n,a*(cap+j))
    if not weight:
        yield 0
        return
    h=min(n,max(1,a*max(1,j)))
    ball=sum(comb(n,i) for i in range(weight+1))
    bias_bits=(weight+8)*(1<<h)
    field_bits=n.bit_length()+bias_bits+1
    if 2*h*field_bits+2>=ball.bit_length():
        for size in range(weight+1):
            for chosen in combinations(range(n),size):
                yield sum(1<<i for i in chosen)
        return
    # q > n*2^(bias_bits+1), so the finite field multiset has bias <=n/q.
    points=prior['seeds'](n,bias_bits)
    # Zero permits padding any subset of at most h elements to exactly h terms.
    for size in range(min(h,len(points))+1):
        for chosen in combinations(points,size):
            yield reduce(xor,chosen,0)
