"""Enumerate labeled real/filler choices and all genuine-cycle markings."""
from itertools import product

def check(mapping):
    n = len(mapping)
    t,s = n,n+1
    u = 0
    visited = set()
    while u < n and u >= 0 and u not in visited:
        visited.add(u)
        u = mapping[u]
    target = int(u==t)
    pos = neg = 0
    for choices in product(range(2),repeat=n):
        pi = [mapping[i] if c else i for i,c in enumerate(choices)]+[s,0]
        if set(pi)!=set(range(n+2)):
            continue
        for marks in product(range(2),repeat=n):
            marked = {i for i,b in enumerate(marks) if b}
            if any(not choices[i] for i in marked) or {pi[i] for i in marked} != marked:
                continue
            inversions = sum(pi[i]>pi[j] for i in marked for j in marked if i<j)
            if (len(marked)+inversions)%2:
                neg+=1
            else:
                pos+=1
    assert pos-neg==target
    return pos,neg,target

stats = [check(mapping) for n in range(1,5)
         for mapping in product(range(-1,n+1),repeat=n)]
for p,m,f in stats[:67]:
    for q,l,g in stats[:67]:
        assert (p*q+m*l)-(p*l+m*q)==f*g
print(len(stats),'functional maps and',67**2,'two-program signed products passed')
