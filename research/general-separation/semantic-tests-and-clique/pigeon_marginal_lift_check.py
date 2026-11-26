"""Exact marginals for the 5-to-4 XOR gadgets and raw AND-parity fibers."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product

def pigeon(i,b):
    return 2*i+b
def diff(i,j,b):
    return 10+2*pairs.index((i,j))+b
def assignment(i,j,a,b):
    result={}
    for k in range(2):
        x,y=(a>>k)&1,(b>>k)&1
        result.update({pigeon(i,k):x,pigeon(j,k):y,diff(i,j,k):x^y})
    return result

def marginal(scope,table,new):
    indices=[scope.index(v) for v in new]
    out=Counter()
    for bits,w in table.items():
        out[tuple(bits[i] for i in indices)]+=w
    return {k:v for k,v in out.items() if v}

pairs=list(combinations(range(5),2))
clauses=[]
records=[]
for i,j in pairs:
    local=[]
    for b in range(2):
        scope=(pigeon(i,b),pigeon(j,b),diff(i,j,b))
        local.extend((scope,vals) for vals in product(range(2),repeat=3)
                     if vals[2] != vals[0]^vals[1])
    local.append(((diff(i,j,0),diff(i,j,1)),(0,0)))
    for scope,bad in local:
        clauses.append((i,j,scope,bad))
        p,z=Counter(),Counter()
        for a,b in permutations(range(4),2):
            raw=assignment(i,j,a,b)
            bits=tuple(raw[v] for v in scope)
            p[bits]+=Fraction(1,12)
            z[bits]+={(0,1):1,(2,1):-1,(2,0):1}.get((a,b),0)
        assert sum(p.values())==sum(z.values())==1 and not p[bad] and not z[bad]
        assert all(not w or p[bits]>0 for bits,w in z.items())
        records.append((scope,p,z))
for a,b in combinations(records,2):
    shared=tuple(sorted(set(a[0]) & set(b[0])))
    for k in (1,2):
        assert marginal(a[0],a[k],shared)==marginal(b[0],b[k],shared)
for left,right in combinations(clauses,2):
    involved=sorted(set(left[:2]+right[:2]))
    for vals in permutations(range(4),len(involved)):
        v=dict(zip(involved,vals))
        for i,j,scope,bad in (left,right):
            raw=assignment(i,j,v[i],v[j])
            assert tuple(raw[x] for x in scope)!=bad
# Every standard basis vector occurs as a point difference within either fiber.
for m in (2,3,4):
    raw=list(product(range(2),repeat=2*m))
    for c in (0,1):
        fiber={x for x in raw if sum(a*b for a,b in zip(x[::2],x[1::2]))%2==c}
        for i in range(2*m):
            assert any(x[:i]+(1-x[i],)+x[i+1:] in fiber for x in fiber)
# Odd charge on a cycle of shared AND features: summing the three equations
# annihilates every feature twice; one charge remains.
for x in product(range(2),repeat=6):
    features=[a*b for a,b in zip(x[::2],x[1::2])]
    syndrome=[features[i]^features[(i+1)%3] for i in range(3)]
    assert syndrome != [1,0,0] and sum(syndrome)%2==0
print('90 clauses, 4005 full intersections and two-event local injections; both fibers through 4 pairs passed')
