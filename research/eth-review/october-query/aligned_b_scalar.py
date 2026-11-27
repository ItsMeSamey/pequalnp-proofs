"""Aligned guarded B sibling, using the physical clause order supplied by the caller."""
from bisect import bisect_left
from dataclasses import dataclass
from collections import Counter

def cycle_order(adj):
    vertices=set(adj)
    v=len(adj)
    deg={len(y) for y in adj.values()}
    if len(deg)!=1: return None
    d=deg.pop()
    if not d or d%2 or d>=v-1: return None
    R=d//2
    if d==v-2:
        pairs=sorted({tuple(sorted((x,next(iter(vertices-adj[x]-{x}))))) for x in vertices})
        seq=[a for a,b in pairs]+[b for a,b in pairs]
    else:
        closed={x:adj[x]|{x} for x in vertices}
        near={x:[y for y in vertices if len(closed[x]^closed[y])==2] for x in vertices}
        if any(len(t)!=2 for t in near.values()): return None
        seq=[min(vertices)]
        visited=set(seq)
        while len(seq)<v:
            opts=[x for x in near[seq[-1]] if x not in visited]
            if not opts: return None
            x=min(opts)
            seq.append(x)
            visited.add(x)
    if any(adj[x]!={seq[(i+j)%v] for j in range(-R,R+1) if j} for i,x in enumerate(seq)): return None
    return tuple(seq),R

@dataclass(frozen=True)
class Leaf:
    n:int
    clauses:tuple
    guard:int
    unit:int
    cycle:tuple
    radius:int

    def weight(self,word,pins=()):
        if not 0<=word<1<<len(self.clauses): raise ValueError('word out of range')
        fixed={}
        for lit in pins:
            if not 1<=abs(lit)<=self.n: raise ValueError('invalid pin')
            if abs(lit) in fixed and fixed[abs(lit)]!=(lit>0): return 0
            fixed[abs(lit)]=int(lit>0)
        g=word>>self.unit&1
        if fixed.get(self.guard,g)!=g: return 0
        spin=set(self.cycle)
        zeros={x for x in spin if fixed.get(x)==0}
        ones={x for x in spin if fixed.get(x)==1}
        for i,c in enumerate(self.clauses):
            if i!=self.unit and word>>i&1: zeros.update(c)
        for i,c in enumerate(self.clauses):
            if i==self.unit or word>>i&1: continue
            a,b=c
            if a in zeros: ones.add(b)
            if b in zeros: ones.add(a)
        if zeros&ones: return 0
        v=len(self.cycle)
        R=self.radius
        free=[i for i,x in enumerate(self.cycle) if x not in zeros|ones]
        count=1
        # Partition nonempty independent sets by smallest selected cyclic index.
        for f in free:
            rest=[i for i in free if f+R<i<f+v-R]
            dp=[1]*(len(rest)+1)
            for j in range(len(rest)-1,-1,-1):
                dp[j]=dp[j+1]+dp[bisect_left(rest,rest[j]+R+1)]
            count+=dp[0]
        free_unused=self.n-v-1-len(set(fixed)-spin-{self.guard})
        return count<<free_unused

    def score(self,rows,trial,pins=(),*,word_cap):
        q=len(self.clauses)
        if word_cap<0: raise ValueError('negative cap')
        piv={}
        for r in (*rows,trial):
            if not 0<=r<1<<q: raise ValueError('row out of range')
            while r:
                j=r.bit_length()-1
                if j not in piv:
                    piv[j]=r
                    break
                r^=piv[j]
        if (1<<(q-len(piv)))>word_cap: return None
        gens=[]
        for i in range(q):
            if i in piv: continue
            w=1<<i
            for j,r in sorted(piv.items()):
                w|=((r&w).bit_count()%2)<<j
            gens.append(w)
        total=w=0
        pins=tuple(pins)
        for i in range(1<<len(gens)):
            if i: w^=gens[(i&-i).bit_length()-1]
            total+=self.weight(w,pins)
        return total

def recognize(n,clauses):
    cs=tuple(tuple(c) for c in clauses)
    units=[i for i,c in enumerate(cs) if len(c)==1]
    if len(units)!=1: return None
    unit=units[0]
    g=-cs[unit][0]
    if not 1<=g<=n: return None
    adj={}
    for i,c in enumerate(cs):
        if i==unit: continue
        if len(c)!=2 or len(set(c))!=2 or g in c or any(not 1<=x<=n for x in c): return None
        a,b=c
        if b in adj.setdefault(a,set()): return None
        adj[a].add(b)
        adj.setdefault(b,set()).add(a)
    layout=cycle_order(adj)
    return None if layout is None else Leaf(n,cs,g,unit,*layout)

def from_original(n,clauses,guard):
    """Construct canonical unit-first B for supplied guard; validate cubic alignment."""
    cs=tuple(tuple(c) for c in clauses)
    if any(len(c)!=3 or len(set(c))!=3 or any(not 1<=x<=n for x in c) for c in cs): return None
    filler=[tuple(x for x in c if x!=guard) for c in cs if guard in c]
    leaf=recognize(n,[(-guard,),*filler])
    if leaf is None: return None
    spin=set(leaf.cycle)
    pairs={frozenset(c) for c in filler}
    real=[c for c in cs if guard not in c]
    count=Counter()
    gates=set()
    used=set()
    for c in real:
        e=frozenset(c)&spin
        z=set(c)-spin
        if len(z)!=1 or e not in pairs or e in used or z&gates: return None
        count.update(e)
        used.add(e)
        gates.update(z)
    return leaf if all(count[x]==3 for x in spin) else None
