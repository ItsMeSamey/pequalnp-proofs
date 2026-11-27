from fractions import Fraction
from itertools import product
from frontier import contract
from endpoint import endpoint

n = 2
rows, kinds = [], {}
for i in range(n):
    kinds[2*i], kinds[2*i+1] = "or", "copy"
    rows.extend([(i,2*i,2*i,True),(i,2*i+1,2*i,False),
                 (i,2*i,2*i+1,True),(i,2*((i-1)%n)+1,2*i+1,True)])
for L,t in product((4,5),map(Fraction,("0","1/3","1"))):
    direct = 0
    for word in product(range(2),repeat=2*n):
        sums = [0]*n
        for p,e,g,pos in rows:
            sums[p] += word[e]
        q = [(1-t)*word[e]+t*Fraction(sums[p],L) for p,e,g,pos in rows]
        w = 1
        for i in range(n):
            a,b,c,d = q[4*i:4*i+4]
            w *= (1-(1-a)*b)*(c*d+(1-c)*(1-d))
        direct += w
    assert direct == contract(rows,kinds,L,t) == contract(rows[::2]+rows[1::2],kinds,L,t)
    if t == 1:
        assert endpoint(rows, kinds, L) == direct
    if t == 0:
        assert direct == 2
print("12 cycle-order comparisons passed")
