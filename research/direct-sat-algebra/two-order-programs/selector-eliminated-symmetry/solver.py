"""Frontier unions with independently recomputed section-based groups."""
from sections import prepare,lift_word
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'selector-prefix-union'))
from prefix_union import insert,lift,remainder

def solve(n,clauses,*,width=4,state_cap=10000):
    raw=tuple(tuple(c) for c in clauses)
    groups={}
    for c in raw:
        if any(not 1<=abs(l)<=n for l in c): raise ValueError('invalid literal')
        if any(-l in c for l in c): continue
        s=tuple(sorted(set(map(abs,c))))
        if len(s)>3: raise ValueError('scope exceeds three')
        groups.setdefault(s,[]).append(c)
    last={v:i for i,s in enumerate(groups) for v in s}
    states=[0]; gs=[]; steps=[]; seen=0; prefix=[]; counts=[]
    for i,(scope,added) in enumerate(groups.items()):
        mask=sum(1<<(v-1) for v in scope)
        shared=seen&mask
        seen|=mask
        newfront=seen&sum(1<<(v-1) for v,j in last.items() if j>i)
        prefix.extend(added)
        _,newsteps,newgs=prepare(n,prefix,newfront,width=width)
        basis={}
        for v,_ in newgs: insert(basis,v,0)
        patch={}; image={}
        for j,(v,_) in enumerate(gs):
            rem,which=insert(patch,v&shared,1<<j)
            if rem: continue
            difference=0
            for k,(u,_) in enumerate(gs):
                if which>>k&1: difference^=u
            quotient,_=remainder(basis,difference&newfront)
            insert(image,quotient,which)
        def realize(h,selection):
            for k,(_,g) in enumerate(gs):
                if selection>>k&1:
                    a,b,d=g
                    if a and ((h>>(a-1))^(h>>(b-1)))&1:
                        h^=(1<<(a-1))|(1<<(b-1))
                    h^=d
            return lift_word(h,steps)
        found={}
        for h in states:
            for t in range(1<<len(scope)):
                a=lift(t,scope)
                if not all(any(bool(a>>(abs(l)-1)&1)==(l>0) for l in c) for c in added): continue
                miss,part=remainder(patch,(h^a)&shared)
                if miss: continue
                if (1<<len(image))>state_cap: return dict(status='skip',counts=counts)
                for index in range(1<<len(image)):
                    choice=part
                    for j,(_,src) in enumerate(image.values()):
                        if index>>j&1: choice^=src
                    w=(realize(h,choice)&(seen&~mask))|a
                    key,_=remainder(basis,w&newfront)
                    found.setdefault(key,w)
                    if len(found)>state_cap: return dict(status='skip',counts=counts)
        states=list(found.values()); gs=newgs; steps=newsteps
        counts.append(len(states))
        if not states: return dict(status='unsat',counts=counts)
    w=states[0]
    if not all(any(bool(w>>(abs(l)-1)&1)==(l>0) for l in c) for c in raw):
        raise AssertionError('raw replay failed')
    return dict(status='sat',witness=w,counts=counts)
