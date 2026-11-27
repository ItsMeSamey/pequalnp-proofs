"""Bijective guard-role separation with original source replay."""
from pathlib import Path
import sys
from time import perf_counter_ns
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'selector-prefix-antichain'))
from prefix import solve,accepts_cnf
from residual import certificate
from directed import TailOrbits,from_forbidden,translate
from coset import tail_equations

def recode(n,raw):
    if type(n) is not int or n<0:raise ValueError('invalid n')
    rows=[]
    for c in raw:
        if any(type(l) is not int or not 1<=abs(l)<=n for l in c):raise ValueError('invalid literal')
        s=set(c)
        if any(-l in s for l in s):continue
        r=tuple(sorted(s,key=abs))
        if len(r)>3:return None
        rows.append(r)
    triples=[r for r in rows if len(r)==3]
    S={abs(r[0]) for r in triples}
    # Preserve hitting while pruning redundant selectors. An indispensable
    # witness at removal time remains indispensable as S only decreases.
    for v in sorted(S,reverse=True):
        if all(any(abs(l)!=v and abs(l) in S for l in r) for r in triples):
            S.remove(v)
    masters=sorted(S)
    edges=set()
    for row in rows:
        hits=sorted(abs(l) for l in row if abs(l) in S)
        for i,v in enumerate(hits):
            edges.update((v,w) for w in hits[i+1:])
    # Endpoints of a maximal matching give a two-approximate vertex cover.
    cover=set()
    for u,v in sorted(edges):
        if u not in cover and v not in cover:cover.update((u,v))
    # Also try an ordinary greedy cover; use the smaller verified cover.
    rest=set(edges); greedy=set()
    while rest:
        degree={}
        for u,v in rest:
            degree[u]=degree.get(u,0)+1;degree[v]=degree.get(v,0)+1
        v=min(degree,key=lambda i:(-degree[i],i))
        greedy.add(v);rest={e for e in rest if v not in e}
    copies=min((cover,greedy),key=lambda C:(len(C),sorted(C)))
    if any(u not in copies and v not in copies for u,v in edges):
        raise AssertionError('uncovered master conflict')
    order=masters+[v for v in range(1,n+1) if v not in S]
    orig={v:i+1 for i,v in enumerate(order)};data=dict(orig)
    for j,v in enumerate(sorted(copies),n+1):data[v]=j
    rec=[]
    for row in rows:
        new=[]
        designated=None
        if len(row)==3:
            hits=sorted(abs(l) for l in row if abs(l) in S)
            designated=next((v for v in hits if v not in copies),hits[0])
        for l in row:
            key=orig if abs(l)==designated else data
            new.append(key[abs(l)] if l>0 else -key[-l])
        rec.append(tuple(new))
    for v in sorted(copies):
        g,d=orig[v],data[v];rec.extend([(-g,d),(g,-d)])
    return rec,orig,data,masters,sorted(copies)

class CheckedTranslation:
    directed=True
    def __init__(self,n):
        self.groups=TailOrbits(n);self.n=n;self.layer=None
        self.strict=0;self.essential=0;self.examined=0;self.first=None
    def __call__(self,j,front,D,E,banks,selectors):
        a,sa=self.groups.key(j,front,D,banks,selectors)
        b,sb=self.groups.key(j,front,E,banks,selectors)
        A=from_forbidden(front,D);B=from_forbidden(front,E)
        shift=sa^sb if a==b else certificate(front,A,B,self.groups.basis)
        self.examined+=1
        if shift is None:return False
        if j!=self.layer:
            tail=[(s if bit==0 else -s,)+tuple(row) for i,s in enumerate(selectors[j:],j+1)
                  for bit,bank in enumerate(banks[i]) for row in bank]
            self.equations=tail_equations(tail,fixed=selectors[:j]);self.layer=j
        if shift.bit_length()>self.n or any((eq&shift).bit_count()%2 for eq in self.equations):
            raise AssertionError('shift fails physical tail or pins')
        proper=False;essential=False
        for scope,table in A.items():
            delta=sum(((shift>>(v-1))&1)<<h for h,v in enumerate(scope))
            image=translate(table,delta)
            if image&~B[scope]:raise AssertionError('shift fails concrete projection inclusion')
            proper|=(image!=B[scope]);essential|=bool(table&~B[scope])
        if proper:
            self.strict+=1
            if essential:
                self.essential+=1
                if self.first is None:self.first=dict(layer=j,frontier=tuple(front),full_shift=shift)
        return True

def solve_cnf(n,clauses,*,state_cap=128):
    start=perf_counter_ns()
    raw=tuple(tuple(c) for c in clauses);chart=recode(n,raw)
    if chart is None:return {'status':'skip','reason':'normalized clause width exceeds three'}
    rec,orig,data,masters,copies=chart
    oracle=CheckedTranslation(n+len(copies))
    r=solve(n+len(copies),rec,state_cap=state_cap,orbit=oracle)
    cost=dict(n=n,original_clauses=len(raw),recoded_clauses=len(rec),recoded_n=n+len(copies),
              masters=masters,copies=copies,strict=oracle.strict,essential_strict=oracle.essential,
              first_essential=oracle.first,comparisons=oracle.examined,stream=r['cost'])
    ans=dict(status=r['status'],route=r['route'],cost=cost)
    if r['status']=='sat':
        y=r['witness'];x=sum(((y>>(q-1))&1)<<(v-1) for v,q in orig.items())
        if any(((y>>(orig[v]-1))^(y>>(data[v]-1)))&1 for v in copies):
            raise AssertionError('physical copy mismatch')
        if not accepts_cnf(raw,x):raise AssertionError('source CNF replay failed')
        ans['witness']=x
    cost['elapsed_ns']=perf_counter_ns()-start
    return ans
