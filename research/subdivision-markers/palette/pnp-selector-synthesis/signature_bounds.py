"""Polynomial exterior upper/lower certificates on a supplied first relation basis."""
from itertools import combinations
from frontier import basis
from wedge_path import wedge
from recognizer import bit_indices

def consistent(cols,indices):
    pivots={}
    for i in indices:
        x,b=cols[i]
        while x:
            top=x.bit_length()-1
            if top not in pivots:
                pivots[top]=(x,b)
                break
            k,t=pivots[top]
            x ^= k
            b ^= t
        if not x and b: return False
    return True

def bounds(cols,L):
    n=len(cols)
    r=len(L)
    signatures=[sum(((v>>i)&1)<<j for j,v in enumerate(L)) for i in range(n)]
    values=sorted(set(signatures)-{0})
    planes={tuple(sorted((a,b,a^b))) for a,b in combinations(values,2)}
    constraints=[]
    for plane in planes:
        if not consistent(cols,[i for i,l in enumerate(signatures) if l in plane]):
            constraints.append(wedge(plane[0],plane[1]))
    lower=[]
    for i,j in combinations(range(r),2):
        if consistent(cols,bit_indices(L[i]|L[j])):
            lower.append(1<<(j*(j-1)//2+i))
    return len(basis(lower)),r*(r-1)//2-len(basis(constraints)),basis(constraints)
