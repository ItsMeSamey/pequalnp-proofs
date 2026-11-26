"""Exact ordinary GF(2) Boolean polynomial-calculus degree, via squarefree monomials."""
from itertools import combinations
from collections import deque
from functools import lru_cache


@lru_cache(None)
def ring(n, degree):
    monomials = tuple(sum(1 << i for i in term)
                      for size in range(degree+1)
                      for term in combinations(range(n),size))
    pos = {mon:i for i,mon in enumerate(monomials)}
    low = sum(mon.bit_count()<degree for mon in monomials)
    multiply = tuple(tuple(1<<pos[mon | (1<<i)] for mon in monomials[:low])
                     for i in range(n))
    return pos, low, multiply


def pc(rows, labels, target, degree, width=3):
    n = len(rows)
    if degree < 2:
        raise ValueError("checker expects a degree of at least two")
    pos, low, multiply = ring(n,degree)
    queue = deque()
    for i,nb in enumerate(rows):
        p = 0
        for j in range(n):
            if nb>>j&1:
                p ^= 1 << pos[(1<<i)|(1<<j)]
        queue.append(p)
    for j in range(width):
        p = (target>>j)&1
        for i,c in enumerate(labels):
            if c>>j&1:
                p ^= 1 << pos[1<<i]
        queue.append(p)
    pivots = {}
    while queue:
        p = queue.popleft()
        while p and p.bit_length() in pivots:
            p ^= pivots[p.bit_length()]
        if p == 1:
            return True
        if not p:
            continue
        pivots[p.bit_length()] = p
        if p.bit_length() <= low:
            terms=[]
            q=p
            while q:
                bit=q&-q
                terms.append(bit.bit_length()-1)
                q^=bit
            for images in multiply:
                product=0
                for k in terms:
                    product ^= images[k]
                queue.append(product)
    return False


def attainable(rows, labels):
    result=set()
    for x in range(1<<len(rows)):
        z=0
        for i,adj in enumerate(rows):
            if x>>i&1:
                if (x&adj).bit_count()%2:
                    break
                z ^= labels[i]
        else:
            result.add(z)
    return result
