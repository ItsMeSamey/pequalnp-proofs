"""Signed CNF compiled through a certified low-weight basis of the observable dual."""
from dataclasses import dataclass
from itertools import combinations
from affine_mst_cnf import add,plug
from affine_mst_complete import enumerate_count
from signed_cover_projection import normalized,sat

@dataclass(frozen=True)
class Chart:
    n:int
    source:tuple
    clauses:tuple
    observables:tuple
    equations:tuple
    checks:tuple
    rank:int
    fiber:int
    probes:int

    def lift(self,w):
        if not 0<=w<1<<len(self.observables): raise ValueError('bad observed word')
        if not self.fiber or not all(sat(c,w) for c in self.clauses): return None
        p={}
        for a,b in self.equations: add(a,b,p)
        for i,x in enumerate(self.observables):
            if not add(1<<(x-1),w>>i&1,p): raise ArithmeticError('unreachable word')
        z=0
        for i,(a,b) in sorted(p.items()):
            if ((z&a).bit_count()%2)^b: z|=1<<i
        if not all(sat(c,z) for c in self.source): raise ArithmeticError('bad witness')
        return z

def compile(n,clauses,*,order,probe_cap,clause_cap):
    if min(n,order,probe_cap,clause_cap)<0: raise ValueError('invalid bounds')
    raw=tuple(tuple(c) for c in clauses)
    if any(not 1<=abs(x)<=n for c in raw for x in c): raise ValueError('bad literal')
    rows=normalized(raw)
    bad=Chart(n,raw,((),),(),(),(),0,0,0)
    if frozenset() in rows: return bad
    piv={}
    eqs=[]
    groups={}
    for c in rows:
        mask=sum(1<<(abs(x)-1) for x in c)
        groups.setdefault((mask,sum(x<0 for x in c)%2),[]).append(c)
    for (mask,p),block in groups.items():
        if len(block)==1<<(mask.bit_count()-1):
            if not add(mask,1^p,piv): return bad
            eqs.append((mask,1^p))
            rows.difference_update(block)
    obs={}
    direct=set()
    for c in sorted(rows,key=lambda s:(len(s),sorted(s))):
        terms=[(x,*plug(1<<(abs(x)-1),0,piv)) for x in sorted(c)]
        false={}
        if not all(add(a,b^(x<0),false) for x,a,b in terms): continue
        local=[]
        for x,a,b in terms:
            if not a: continue
            if a not in obs: obs[a]=(len(obs),abs(x),b)
            i,_,base=obs[a]
            local.append(-(i+1) if b^base^(x<0) else i+1)
        if not local: return bad
        direct.add(tuple(sorted(set(local))))
        if len(direct)>clause_cap: return None
    masks=list(obs)
    t=len(masks)
    rankp={}
    for a in masks: add(a,0,rankp)
    r=len(rankp)
    dual={}
    checks=[]
    probes=0
    for size in range(1,min(order,t)+1):
        if len(dual)==t-r: break
        for ids in combinations(range(t),size):
            if probes>=probe_cap: return None
            probes+=1
            a=b=h=0
            for i in ids:
                a^=masks[i]
                b^=obs[masks[i]][2]
                h|=1<<i
            if a or not plug(h,0,dual)[0]: continue
            add(h,0,dual)
            checks.append((h,b))
            if len(direct)+(1<<(size-1))>clause_cap: return None
            for v in range(1<<size):
                if v.bit_count()%2!=b:
                    direct.add(tuple(-(i+1) if v>>j&1 else i+1 for j,i in enumerate(ids)))
            if len(dual)==t-r: break
    if len(dual)!=t-r: return None
    return Chart(n,raw,tuple(sorted(direct)),tuple(obs[a][1] for a in masks),tuple(eqs),
                 tuple(checks),r,1<<(n-len(piv)-r),probes)

def solve(n,clauses,*,order,probe_cap,clause_cap,backend=enumerate_count):
    """Same exact (count,witness) backend on the chart or unchanged original input."""
    raw=tuple(tuple(c) for c in clauses)
    chart=compile(n,raw,order=order,probe_cap=probe_cap,clause_cap=clause_cap)
    if chart is not None and not chart.fiber: return dict(route='chart',count=0,witness=None)
    d,cs=(len(chart.observables),chart.clauses) if chart is not None else (n,raw)
    count,w=backend(d,cs)
    if not isinstance(count,int) or not 0<=count<=1<<d or (count==0)!=(w is None):
        raise ValueError('invalid backend count or witness')
    if w is not None and (not 0<=w<1<<d or not all(sat(c,w) for c in cs)):
        raise ValueError('bad backend witness')
    return dict(route='original' if chart is None else 'chart',
                count=count if chart is None else count*chart.fiber,
                witness=w if chart is None or w is None else chart.lift(w))
