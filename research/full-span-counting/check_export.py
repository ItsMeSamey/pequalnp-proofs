#!/usr/bin/env python3
"""Independent sparse-polynomial export and weighted signed cube contraction."""
from fractions import Fraction as F
from itertools import product
from random import Random


def combine(terms):
    out={}
    for key,c in terms:
        out[key]=out.get(key,0)+c
    return {k:c for k,c in out.items() if c}


def multiply(a,b):
    return combine((i|j,x*y) for i,x in a.items() for j,y in b.items())


def ev(poly,v):
    return sum(c for k,c in poly.items() if k&v==k)


def export(f,m,E):
    # Upset evaluation on E is triangular in a linear extension of inclusion.
    h={}
    for v in sorted(E,key=int.bit_count):
        assert v
        h[v]=F(1,v.bit_count())-ev(h,v)
    err=combine([(0,1)]+[(k,-c) for k,c in f.items()])
    corr=multiply(multiply({1<<i:1 for i in range(m)},err),h)
    return combine(list(err.items())+[(k,-c) for k,c in corr.items()])


def cubes(poly,rules):
    terms=[]
    for k,c in poly.items():
        pos=neg=0
        for i,(p,n) in enumerate(rules):
            if k>>i&1:
                pos|=p
                neg|=n
        if not pos&neg:
            terms.append(((pos,neg),c))
    return combine(terms)


def holds(cube,x):
    pos,neg=cube
    return x&pos==pos and not x&neg


def pattern(rules,x):
    return sum(1<<i for i,cube in enumerate(rules) if holds(cube,x))


def contract(factors):
    merged={(0,0):1}
    for factor in factors:
        merged=combine((((p|u,n|v),c*d) for (p,n),c in merged.items()
                        for (u,v),d in factor.items() if not (p|u)&(n|v)))
    return merged


def main():
    rng=Random(9298)
    outside=0
    # Deterministic off-core witness: core pins x1=0, single fault x1, f=0, E empty.
    assert export({},1,[])=={0:1} and ev(export({},1,[]),1)!=0
    for case in range(60):
        n=5
        # Core (x0 OR x1) AND NOT(x2 AND x3), local factor x4 OR NOT x0.
        core=lambda x: bool(x&3) and (x&12)!=12
        local={(0,0):1,(1,16):-1}
        factors=[]
        rule_sets=[]
        for idx in range(3):
            rules=[]
            for _ in range(4):
                digits=[rng.choice((-1,0,1,1)) for _ in range(n)]
                rules.append((sum(1<<i for i,k in enumerate(digits) if k==0),
                              sum(1<<i for i,k in enumerate(digits) if k==-1)))
            rule_sets.append(rules)
            f={1<<j:F(rng.randint(-2,3),rng.randint(1,4)) for j in range(len(rules))}
            assert ev(f,0)==0
            E={v for x in range(1<<n) if core(x)
               for v in [pattern(rules,x)] if v and ev(f,v)!=1}
            poly=export(f,len(rules),E)
            signed=cubes(poly,rules)
            factors.append(signed)
            for x in range(1<<n):
                v=pattern(rules,x)
                val=sum(c for cube,c in signed.items() if holds(cube,x))
                assert val==ev(poly,v)
                if core(x):
                    assert val==int(not v)
                else:
                    outside+=val!=int(not v)
        joint=contract(factors+[local])
        total=sum(c*sum(core(x) and holds(cube,x) for x in range(1<<n))
                  for cube,c in joint.items())
        brute=0
        for x in range(1<<n):
            if core(x):
                expected=int((x&1)==0 or bool(x&16)) * all(not pattern(r,x) for r in rule_sets)
                assert sum(c for cube,c in joint.items() if holds(cube,x))==expected
                brute+=expected
        assert total==brute
    assert outside
    print(f"60 overlapping exports, 180 learned factors, pointwise and joint exact; {outside} off-core discrepancies.")


if __name__=='__main__':
    main()
