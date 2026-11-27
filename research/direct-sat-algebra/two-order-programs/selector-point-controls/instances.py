"""Precommitted three-color discrepancy cases in original DIMACS names."""
from itertools import combinations, product


def original(h, yes):
    sites=3*h
    data=lambda color,i:sites+color*h+i+1
    gate=lambda color,i:color*h+i+1
    carry=lambda color,i:2*sites+color*(h+1)+i+1
    rows=[]
    for c in range(3):
        for i,j in combinations(range(h),2):
            rows.append((-data(c,i),-data(c,j)))
    for i,j in product(range(h),repeat=2):
        for a,b,ok in ((0,1,i<=j),(1,2,i<=j),(2,0,i<j or (yes and i==j==h//2))):
            if not ok:
                rows.append((-data(a,i),-data(b,j)))
    for c in range(3):
        rows.extend([(-carry(c,0),),(carry(c,h),)])
        for i in range(h):
            g,x=gate(c,i),data(c,i)
            rows.extend([(-g,x),(g,-x)])
            scope=(carry(c,i),g,carry(c,i+1))
            for values in product(range(2),repeat=3):
                if sum(values)%2:
                    rows.append(tuple(-v if b else v for v,b in zip(scope,values)))
    return 3*sites+3,rows
