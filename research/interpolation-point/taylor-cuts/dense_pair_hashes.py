"""Deterministic perfect hashes for planted k-subsets with O(k) colors."""
from functools import lru_cache
from itertools import combinations, product
from math import factorial, isqrt


def prime_at_least(n):
    p=max(2,n)
    while any(p%d==0 for d in range(2,isqrt(p)+1)):
        p+=1
    return p


@lru_cache(maxsize=8)
def small_family(q,t):
    if t==1:
        return ((0,)*q,)
    uncovered=list(combinations(range(q),t))
    prob=[factorial(t-a)*t**a for a in range(t+1)]
    result=[]
    while uncovered:
        colors=[]
        for x in range(q):
            scores=[0]*t
            for subset in uncovered:
                if x not in subset:
                    continue
                used=[colors[y] for y in subset if y<x]
                if len(set(used))<len(used):
                    continue
                for c in range(t):
                    if c not in used:
                        scores[c]+=prob[len(used)+1]
            colors.append(max(range(t),key=scores.__getitem__))
        result.append(tuple(colors))
        rem=[s for s in uncovered if len({colors[x] for x in s})<t]
        if len(rem)==len(uncovered):
            raise ArithmeticError("cover failed to progress")
        uncovered=rem
    return tuple(result)


def colorings(n,k):
    if type(n) is not int or type(k) is not int or n<0 or k<0:
        raise ValueError("nonnegative integer dimensions required")
    k=min(n,k)
    if k<=1:
        yield (0,)*n
        return
    if n<=2*k:
        yield tuple(range(n))
        return
    q=min(n,4*k*k)
    t=max(1,k.bit_length()-1)
    blocks=(k+t-1)//t
    family=small_family(q,t)
    p=prime_at_least(n)
    multipliers=(0,) if n==q else range(1,p)
    for a in multipliers:
        compressed=tuple(range(n)) if a==0 else tuple((a*x%p)%q for x in range(n))
        for cuts in combinations(range(1,q),blocks-1):
            bounds=(0,)+cuts+(q,)
            for choice in product(family,repeat=blocks):
                table=tuple(block*t+choice[block][x]
                            for block in range(blocks)
                            for x in range(bounds[block],bounds[block+1]))
                yield tuple(table[x] for x in compressed)
