from itertools import combinations
from random import Random
from functools import reduce
from operator import xor

def span(E):
    s={0}
    for x in E:s.update(x^y for y in tuple(s))
    return s
def subsets(E):
    return [t for n in range(len(E)+1) for t in combinations(E,n)]
U=set(range(16))
H={0,1,2,3}
def feasible(E,pinned=()):
    return any(span((*pinned,*X))&U==H for X in subsets(E))
def reducer(E):
    E=[x for x in set(E) if x and (x not in U or x in H)]
    for h in H&set(E):return feasible(E,[h])
    for q in {x>>2 for x in E}:
        B=[x for x in E if x>>2==q]
        if len(B)>1:
            if feasible(E,B[:2]):return True
            E=[x for x in E if x not in B]
    return feasible(E)
rng=Random(61741)
for _ in range(150):
    E=rng.sample(range(64),rng.randrange(3,10))
    assert reducer(E)==feasible(E)
E=(16,32,49,64,81)
cycles=[set(C) for C in subsets(E) if C and reduce(xor,C)>>2==0]
circuits=[c for c in cycles if not any(d<c for d in cycles)]
assert circuits==[{16,32,49},{16,64,81},{32,49,64,81}]
assert not feasible(E)
print('150 bucket comparisons and elimination counterexample passed')
