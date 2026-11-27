"""Direct tests of rank peeling on attainable GF(3)^2 sets with distinct baselines."""
from itertools import combinations,product
from random import Random

V=frozenset(product(range(3),repeat=2))
zero=(0,0)
def add(v,w):
    return tuple((x+y)%3 for x,y in zip(v,w))
def neg(v):
    return tuple(-x%3 for x in v)
def sums(a,b):
    return {add(v,w) for v in a for w in b}
def span(tokens):
    out={zero}
    for d in tokens:
        out=sums(out,{zero,d,neg(d)})
    return frozenset(out)
lines=set(span([x]) for x in V-{zero})
spaces=[frozenset([zero]),*lines,V]
def dim(U):
    return {1:0,3:1,9:2}[len(U)]

def verify(slots,s=3):
    baselines=[v[0] for v in slots]
    diffs=[{add(x,neg(t[0])) for x in t} for t in slots]
    U=min(spaces,key=lambda W:s*dim(W)+sum(not d<=W for d in diffs))
    exceptional=[i for i,d in enumerate(diffs) if not d<=U]
    internal=[i for i,d in enumerate(diffs) if d<=U]
    assert len(exceptional)<=s*(2-dim(U))
    bases=[]
    for ids in combinations(internal,dim(U)):
        for ds in product(*(diffs[i] for i in ids)):
            if span(ds)==U:
                bases.append((set(ids),ds))
                break
    def pack(left,used,ds):
        if left==0:
            return ds
        for ids,vectors in bases:
            if not used&ids:
                found=pack(left-1,used|ids,ds+vectors)
                if found is not None:
                    return found
    toggles=pack(s,set(),())
    assert toggles is not None
    attainable={zero}
    for d in toggles:
        attainable=sums(attainable,{zero,d})
    assert attainable==U
    exact={zero}
    predicted=set(U)
    for i,t in enumerate(slots):
        exact=sums(exact,t)
        predicted=sums(predicted,t if i in exceptional else [baselines[i]])
    assert exact==predicted
    return dim(U)


if __name__=='__main__':
    rng=Random(108705)
    counts=[0,0,0]
    for seed in range(700):
        slots=[]
        for _ in range(rng.randrange(14)):
            base=rng.choice(sorted(V))
            pool=rng.choice(spaces if seed%3 else [frozenset([zero]),spaces[1]])
            ds=rng.sample(sorted(pool-{zero}),rng.randrange(min(3,len(pool)-1)+1))
            slots.append([base]+[add(base,v) for v in ds])
        counts[verify(slots)]+=1
    assert min(counts)>0
    print("700 slot systems: exact profiles, disjoint generators and toggle coverage passed",counts)
