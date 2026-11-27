"""Exact affine unions of reachable original frontier words."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'selector-coset-native'))
from coset import equations_for_group, insert, kernel, lift


def remainder(rows,value):
    shift=0
    for p in sorted(rows,reverse=True):
        if value>>p&1:
            x,y=rows[p]
            value^=x
            shift^=y
    return value,shift


def solve(n,clauses,*,state_cap=10000,inspect=False):
    raw=tuple(tuple(c) for c in clauses)
    factors={}
    for clause in raw:
        if any(not 1<=abs(v)<=n for v in clause):
            raise ValueError('invalid literal')
        if any(-v in clause for v in clause):
            continue
        scope=tuple(sorted(set(map(abs,clause))))
        if len(scope)>3:
            raise ValueError('scope exceeds three')
        bad=sum(1<<j for j,v in enumerate(scope) if -v in clause)
        factors[scope]=factors.get(scope,(1<<(1<<len(scope)))-1)&~(1<<bad)
    last={v:i for i,scope in enumerate(factors) for v in scope}
    states={0:0}
    seen=0
    equations=set()
    history=[]
    for i,(scope,table) in enumerate(factors.items()):
        mask=sum(1<<(v-1) for v in scope)
        shared=mask&seen
        patch={}
        for u in kernel(n,equations):
            insert(patch,u&shared,u)
        equations.update(equations_for_group(scope,table))
        seen|=mask
        front=seen&sum(1<<(v-1) for v in last if last[v]>i)
        orbits={}
        for u in kernel(n,equations):
            insert(orbits,u&front,u)
        next_states={}
        for word in states.values():
            for t in range(1<<len(scope)):
                if not table>>t&1:
                    continue
                tupleword=lift(t,scope)
                miss,shift=remainder(patch,(tupleword^word)&shared)
                if miss:
                    continue
                witness=((word^shift)&(seen&~mask))|tupleword
                key,_=remainder(orbits,witness&front)
                next_states.setdefault(key,witness)
                if len(next_states)>state_cap:
                    return dict(status='skip',layers=history)
        states=next_states
        if inspect:
            history.append((front,tuple(x for x,_ in orbits.values()),tuple(states)))
        if not states:
            return dict(status='unsat',layers=history)
    word=next(iter(states.values()))
    if not all(any(bool(word>>(abs(l)-1)&1)==(l>0) for l in c) for c in raw):
        raise AssertionError('raw replay failed')
    return dict(status='sat',witness=word,layers=history)
