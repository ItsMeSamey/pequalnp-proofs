"""Reachable original frontier cosets with signed-permutation lifts."""
from pathlib import Path
import sys
from swaps import signed_swaps,insert,lift
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'selector-prefix-union'))
from prefix_union import remainder

def permute(p,w):
    return sum(((w>>i)&1)<<j for i,j in enumerate(p))

def compose(g,h):
    p,u=g
    q,v=h
    return tuple(p[j] for j in q),permute(p,v)^u

def solve(n,clauses,*,state_cap=10000):
    raw=tuple(tuple(c) for c in clauses)
    grouped={}
    for c in raw:
        if any(not 1<=abs(l)<=n for l in c): raise ValueError('bad literal')
        if any(-l in c for l in c): continue
        s=tuple(sorted(set(map(abs,c))))
        if len(s)>3: raise ValueError('scope exceeds three')
        bad=sum(1<<j for j,v in enumerate(s) if -v in c)
        grouped[s]=grouped.get(s,(1<<(1<<len(s)))-1)&~(1<<bad)
    last={v:i for i,s in enumerate(grouped) for v in s}
    identity=tuple(range(n)),0
    def product(bits,gs):
        g=identity
        while bits:
            low=bits&-bits
            g=compose(gs[low.bit_length()-1],g)
            bits^=low
        return g
    states=[0]; gens=[]; seen=0; tables={}; counts=[]
    for i,(scope,tab) in enumerate(grouped.items()):
        mask=sum(1<<(v-1) for v in scope)
        shared=seen&mask
        patch={}; inherited=[]
        for j,g in enumerate(gens):
            rem,which=insert(patch,g[1]&shared,1<<j)
            if not rem: inherited.append(product(which,gens))
        seen|=mask
        front=seen&sum(1<<(v-1) for v in last if last[v]>i)
        tables[scope]=tab
        candidates=inherited[:]
        for _,(x,y,d) in signed_swaps(n,tables,front):
            p=list(identity[0])
            if x: p[x-1],p[y-1]=p[y-1],p[x-1]
            candidates.append((tuple(p),d&seen))
        basis={}; newgens=[]
        for g in candidates:
            rem,_=insert(basis,g[1]&front,0)
            if rem: newgens.append(g)
        found={}
        for h in states:
            for iword in range(1<<len(scope)):
                if not tab>>iword&1: continue
                a=lift(iword,scope)
                miss,which=remainder(patch,(h^a)&shared)
                if miss: continue
                p,d=product(which,gens)
                w=((permute(p,h)^d)&(seen&~mask))|a
                key,_=remainder(basis,w&front)
                found.setdefault(key,w)
                if len(found)>state_cap: return dict(status='skip',counts=counts)
        states=list(found.values()); gens=newgens; counts.append(len(states))
        if not states: return dict(status='unsat',counts=counts)
    w=states[0]
    if not all(any(bool(w>>(abs(l)-1)&1)==(l>0) for l in c) for c in raw):
        raise AssertionError('raw replay failed')
    return dict(status='sat',witness=w,counts=counts)
