"""Bounded original-support and module checks intended for scheduler 04."""
from itertools import product,permutations
from random import Random
from modular_support import nonzero,in_span

def value(row,layers,terminal,w,mod):
    for bit,choices in zip(w,layers):
        matrix=choices[bit]
        row=tuple(sum(a*matrix[i][j] for i,a in enumerate(row))%mod for j in range(len(matrix[0])))
    return sum(a*b for a,b in zip(row,terminal))%mod

def verify():
    rng=Random(72319)
    for b in [1,2,3]:
        m=1<<b
        for _ in range(24):
            width=rng.randrange(1,4)
            def row():return tuple(rng.randrange(m) for _ in range(width))
            generators=[row() for _ in range(rng.randrange(1,4))]
            target=row()
            expected=any(all(sum(c*g[j] for c,g in zip(combo,generators))%m==t for j,t in enumerate(target)) for combo in product(range(m), repeat=len(generators)))
            assert in_span(generators,target,b)==expected
            start,end=row(),row()
            layers=[[[row() for _ in range(width)] for bit in range(2)] for _ in range(4)]
            got=nonzero(start,layers,end,b)
            exp=any(value(start,layers,end,w,m) for w in product((0,1),repeat=4))
            assert (got is not None)==exp
            if got is not None:assert value(start,layers,end,got,m)
    d=3
    edges=list(product(range(d),range(d,2*d)))
    supports={}
    def flat(selected):
        comp=list(range(2*d))
        for u,v in selected:
            lo,hi=sorted((comp[u],comp[v]))
            comp=[lo if c==hi else c for c in comp]
        return tuple(comp)
    for bits in product((0,1),repeat=len(edges)):
        selected=[edge for edge,bit in zip(edges,bits) if bit]
        key=flat(selected)
        supports[key]=supports.get(key,0)+1
    for pi in permutations(range(d,2*d)):
        assert supports[flat(zip(range(d),pi))]==1
    # Direct original gate evaluation and projected expansion on K_2,2, mod 4.
    edge2=[(0,2),(0,3),(1,2),(1,3)]
    for x,y in product(range(16),repeat=2):
        op=[int((x>>u^x>>v)&1==0 and (y>>u^y>>v)&1==0) for u,v in edge2]
        direct=int(len(set(op))==1)
        combined=(1+(-1)**4)*int(all(op))
        for mask in range((1<<4)-1):
            combined+=(-1)**mask.bit_count()*int(all(op[j] for j in range(4) if mask>>j&1))
        assert combined==direct
    print('72 module memberships, 72 raw-word weighted programs, 6 matching keys, 256 original normalized gate replays passed')
if __name__=='__main__':verify()
