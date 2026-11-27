"""Decision projection of signed CNF onto a primal vertex cover."""
from dataclasses import dataclass

def normalized(raw):
    out=set()
    for clause in raw:
        c=frozenset(clause)
        if not any(-x in c for x in c): out.add(c)
    return out

def sat(c,w):
    return any(bool(w>>(abs(x)-1)&1)==(x>0) for x in c)

@dataclass(frozen=True)
class Projection:
    n:int
    source:tuple
    core:tuple
    clauses:tuple
    pairs:int

    def lift(self,word):
        if not 0<=word<1<<len(self.core): raise ValueError('bad core word')
        if not all(sat(c,word) for c in self.clauses): return None
        x=sum(((word>>j)&1)<<(v-1) for j,v in enumerate(self.core))
        core=set(self.core)
        forced={}
        for c in normalized(self.source):
            if sat((v for v in c if abs(v) in core),x): continue
            residual=[v for v in c if abs(v) not in core]
            if len(residual)!=1: raise ArithmeticError('bad projection')
            v=residual[0]
            if abs(v) in forced and forced[abs(v)]!=(v>0): raise ArithmeticError('bad lift')
            forced[abs(v)]=v>0
        for v,b in forced.items():
            if b: x|=1<<(v-1)
        if not all(sat(c,x) for c in self.source): raise ArithmeticError('source mismatch')
        return x

def project(n,clauses,*,cover=None,pair_cap=None):
    if n<0 or pair_cap is not None and pair_cap<0: raise ValueError('invalid bounds')
    raw=tuple(tuple(c) for c in clauses)
    if any(not 1<=abs(x)<=n for c in raw for x in c): raise ValueError('bad literal')
    rows=sorted(normalized(raw),key=lambda c:(len(c),sorted(c)))
    if cover is None:
        chosen=set()
        for c in rows:
            free=sorted(abs(x) for x in c if abs(x) not in chosen)
            for j in range(0,len(free)-1,2): chosen.update(free[j:j+2])
    else:
        chosen=set(cover)
        if any(not 1<=x<=n for x in chosen): raise ValueError('invalid cover')
    core=tuple(sorted(chosen))
    ids={x:i+1 for i,x in enumerate(core)}
    out=set()
    buckets={}
    for c in rows:
        outside=[x for x in c if abs(x) not in ids]
        if len(outside)>1: raise ValueError('uncovered edge')
        rest=frozenset(ids[abs(x)]*(1 if x>0 else -1) for x in c if abs(x) in ids)
        if outside:
            x=outside[0]
            buckets.setdefault(abs(x),([],[]))[x>0].append(rest)
        else: out.add(rest)
    pairs=0
    for neg,pos in buckets.values():
        if frozenset() in out: break
        for a in neg:
            for b in pos:
                if pair_cap is not None and pairs>=pair_cap: return None
                pairs+=1
                r=a|b
                if not any(-x in r for x in r): out.add(r)
                if not r: break
            if frozenset() in out: break
    if frozenset() in out: out={frozenset()}
    encoded=tuple(sorted((tuple(sorted(c)) for c in out),key=lambda c:(len(c),c)))
    return Projection(n,raw,core,encoded,pairs)
