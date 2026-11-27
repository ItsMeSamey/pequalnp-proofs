"""Fano physical-tree LP, exhaustive paths and rationally checked primal/dual."""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
from pathlib import Path
import json
import warnings
import argparse
import numpy as np
from scipy.optimize import linprog, OptimizeWarning
from scipy.sparse import coo_matrix

N=7
edges=[(p,l) for p,l in product(range(N),repeat=2) if (p-l)%N in (0,1,3)]
class Circuit:
    def __init__(self):
        self.ops={}
        self.collect=[]
    def gate(self,op,a,b):
        v=14+len(self.ops)
        self.ops[v]=(op,a,b)
        return v
    def join(self,ws,collector=False):
        head,*tail=ws
        for w in tail:
            head=self.gate('|',head,w)
            if collector: self.collect.append(head)
        return head

def build(kind):
    c=Circuit()
    terms=[]
    def star(raw,others):
        terms.append(c.gate('&',raw,c.join(others)))
    if kind in ('star','dual','split','balanced'):
        for v in range(N):
            ns=([7+l for p,l in edges if p==v] if kind!='dual' else
                [p for p,l in edges if l==v])
            if kind=='balanced': ns=[j for j in ns if j!=7+v]+[7+v]
            owner=v if kind!='dual' else v+7
            if kind=='split':
                first=c.gate('&',owner,ns[0])
                second=c.gate('&',owner,c.join(ns[1:]))
                terms.append(c.gate('|',first,second))
            else: star(owner,ns)
    elif kind=='hybrid':
        A={p for p,l in edges if l==0}
        for p in sorted(A): star(p,[7+l for u,l in edges if u==p])
        for l in range(N):
            ns=[p for p,y in edges if y==l and p not in A]
            if ns: star(l+7,ns)
    elif kind=='shared':
        p=0
        l=next(y for y in range(N) if (p,y) not in edges)
        a=next(u for u,y in edges if y==l)
        l0=next(y for u,y in edges if u==p and (a,y) in edges)
        work=[y for u,y in edges if u==p and y!=l0]
        for u in range(N):
            if u in (p,a): continue
            ns=[7+y for x,y in edges if x==u and y!=l]
            if ns: star(u,ns)
        g=c.gate('&',c.join([p,a]),c.join([p,7+l0,7+l]))
        for y in work:
            u=next(u for u,j in edges if j==y and (u,l) in edges)
            terms.append(c.gate('&',c.join([g,u]),c.join([7+y,c.gate('&',u,7+l)])))
        terms.append(c.gate('&',c.gate('&',g,c.join([a,7+l0])),c.join([7+l,7+l0])))
        star(a,[7+y for u,y in edges if u==a and y not in (l,l0)])
    else: raise ValueError(kind)
    root=c.join(terms,True)
    return c,root,set(c.collect[-6:])

def trees(c,root,face):
    p,l=face
    active={u for u,v in edges if v==l and u!=p}|{v+7 for u,v in edges if u==p and v!=l}
    rep={u:(None if u in active else u) for u in range(14)}
    # None is the constant one. Keep original IDs at binary residual gates.
    live={}
    for v,(op,x,y) in c.ops.items():
        a,b=rep[x],rep[y]
        if a is None or b is None:
            rep[v]=None if op=='|' else (b if a is None else a)
        elif a==b:
            rep[v]=a
        else:
            live[v]=(op,a,b)
            rep[v]=v
    root=rep[root]
    assert root is not None
    # All simple raw-to-root paths, recorded as triples (node,reader,pin).
    paths=defaultdict(list)
    def visit(v,rev):
        if v<14:
            paths[v].append(tuple(reversed(rev)))
        else:
            op,a,b=live[v]
            for pin,u in enumerate((a,b)):
                visit(u,rev+[(u,v,pin)])
    visit(root,[])
    assert set(paths)==set(range(14))-active
    found=set()
    def merge(i,succ,slots):
        if i==len(options):
            ids=tuple(sorted(v for v,m in slots.items() if m==3))
            assert len(ids)==9
            found.add(ids)
            return
        for path in options[i]:
            new_succ=succ.copy()
            new_slots=slots.copy()
            for u,v,pin in path:
                edge=(v,pin)
                if u in new_succ and new_succ[u]!=edge: break
                new_succ[u]=edge
                m=new_slots.get(v,0) | (1<<pin)
                if m==3 and live[v][0]=='&': break
                new_slots[v]=m
            else: merge(i+1,new_succ,new_slots)
    options=sorted(paths.values(),key=len)
    merge(0,{}, {})
    assert found
    return found

def full_cube(c,root):
    rows=1<<14
    raw=[((1<<rows)-1)//((1<<(1<<i))+1) << (1<<i) for i in range(14)]
    v=raw.copy()
    for op,a,b in c.ops.values():
        v.append(v[a]|v[b] if op=='|' else v[a]&v[b])
    target=0
    for p,l in edges:
        target |= raw[p]&raw[7+l]
    assert target==v[root]

def solve(kind, cert=None):
    c,root,J=build(kind)
    full_cube(c,root)
    pool=sorted(v for v,(op,_,_) in c.ops.items() if op=='|' and v not in J)
    index={v:i for i,v in enumerate(pool)}
    faces=[sorted({tuple(i for i in T if i not in J) for T in trees(c,root,f)}) for f in edges]
    n=sum(map(len,faces))
    rr=[]; cc=[]; er=[]; ec=[]
    j=0
    for f,opts in enumerate(faces):
        for opt in opts:
            er.append(f);ec.append(j)
            for i in opt: rr.append(index[i]);cc.append(j)
            j+=1
    A=coo_matrix(([1]*len(rr)+[-1]*len(pool),(rr+list(range(len(pool))),cc+[n]*len(pool))),shape=(len(pool),n+1))
    E=coo_matrix(([1]*len(er),(er,ec)),shape=(21,n+1))
    if cert is None:
        with warnings.catch_warnings():
            warnings.filterwarnings('ignore',message='Unrecognized options.*',category=OptimizeWarning)
            res=linprog([0]*n+[1],A_ub=A,b_ub=np.zeros(len(pool)),A_eq=E,b_eq=np.ones(21),bounds=(0,None),method='highs',options={'threads':1})
        assert res.success,res.message
        rat=lambda x:F(float(x)).limit_denominator(10**6)
        B=rat(res.x[-1])
        w=list(map(rat,res.x[:-1]))
        lam=list(map(lambda x:rat(-x),res.ineqlin.marginals))
    else:
        B=F(cert['B'])
        w=[F(0)]*n
        for col,x in cert['primal']: w[col]=F(x)
        lam=[F(cert['dual'].get(str(v),'0')) for v in pool]
    load=[F(0)]*len(pool); dual=F(0); j=0
    assert min(lam)>=0 and sum(lam)<=1
    for opts in faces:
        ps=w[j:j+len(opts)];j+=len(opts)
        assert min(ps)>=0 and sum(ps)==1
        for opt,wt in zip(opts,ps):
            for v in opt: load[index[v]]+=wt
        dual+=min(sum(lam[index[v]] for v in opt) for opt in opts)
    assert max(load)==B==dual
    proof={'B':str(B), 'primal':[(j,str(x)) for j,x in enumerate(w) if x], 'dual':{v:str(x) for v,x in zip(pool,lam) if x}}
    print(f'{kind}: gates={len(c.ops)} J={sorted(J)} choices={n} range={min(map(len,faces))}..{max(map(len,faces))} B={B} primal={max(load)} dual={dual}')

    return proof

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('cases',nargs='*')
    parser.add_argument('--replay',action='store_true')
    parser.add_argument('--save',action='store_true')
    args=parser.parse_args()
    path=Path(__file__).with_name('flexible-face-lp-control-certificates.json')
    existing=json.loads(path.read_text()) if args.replay else {}
    out={}
    for kind in args.cases or ['star','balanced','dual','split','hybrid','shared']:
        out[kind]=solve(kind,existing[kind] if args.replay else None)
    if args.save: path.write_text(json.dumps(out,indent=1,sort_keys=True)+'\n')
