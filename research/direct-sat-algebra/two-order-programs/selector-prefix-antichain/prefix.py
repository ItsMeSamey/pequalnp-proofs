"""Decision-only antichain of existentially projected binary prefix relations."""
from itertools import combinations,product
from pathlib import Path
from time import perf_counter_ns
import sys
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'guard-cap-review/cnf-two-state'))
from recognizer import binary_model
sys.path.insert(0,str(ROOT/'direct-sat-portfolio'))
from original_cnf import accepts_cnf


def diagram(n,rows,sites,cost):
    def possible(pins):
        cost['binary_probes']+=1
        return binary_model(n,rows+[(l,) for l in pins]) is not None
    if not possible(()):return None
    bad=set()
    for size in (1,2):
        for group in combinations(sites,size):
            for values in product((0,1),repeat=size):
                pins=tuple(j if v else -j for j,v in zip(group,values))
                if not possible(pins):bad.add(tuple(-l for l in pins))
    return frozenset(bad)


def solve(n,clauses,*,dominance=True,state_cap=1024,orbit=None):
    start=perf_counter_ns()
    if type(n) is not int or n<0 or type(state_cap) is not int or state_cap<1:raise ValueError('invalid limit')
    raw=tuple(tuple(c) for c in clauses)
    if any(type(l) is not int or not 1<=abs(l)<=n for row in raw for l in row):raise ValueError('invalid literal')
    cost=dict(n=n,raw_clauses=len(raw),layers=[],binary_probes=0,highwater=0)
    def finish(status,reason,w=None):
        if status=='sat' and not accepts_cnf(raw,w):raise AssertionError('raw witness failed')
        cost['elapsed_ns']=perf_counter_ns()-start
        return dict(status=status,route=reason,witness=w,cost=cost)
    norm=[tuple(sorted(set(row),key=abs)) for row in raw if all(-v not in row for v in row)]
    if any(len(row)>3 for row in norm):return finish('skip','raw width')
    selectors=sorted({abs(row[0]) for row in norm if len(row)==3})
    S=set(selectors);idx={s:i+1 for i,s in enumerate(selectors)}
    banks=[[[],[]] for _ in range(1+len(S))]
    for row in norm:
        guards=[l for l in row if abs(l) in S]
        if len(guards)>1:return finish('skip','proposed decomposition has multiple guards')
        if guards:
            guard=guards[0]
            banks[idx[abs(guard)]][int(guard<0)].append(tuple(l for l in row if l!=guard))
        else:banks[0][0].append(row)
    scopes=[{abs(l) for bank in step for row in bank for l in row} for step in banks]
    tails=[set() for _ in banks]
    for j in reversed(range(len(banks)-1)):tails[j]=tails[j+1]|scopes[j+1]
    states=[(frozenset(),0)];seen=set()
    for j,(rows0,rows1) in enumerate(banks):
        seen|=scopes[j];front=sorted(seen&tails[j])
        next_states=[];candidates=0
        for prev,word in states:
            for v,add in enumerate((rows0,rows1) if j else (rows0,)):
                candidates+=1
                D=diagram(n,list(prev)+add,front,cost)
                if D is None:continue
                if any((E<=D if dominance else E==D) for E,_ in next_states):continue
                if orbit and any(orbit(j,front,D,E,banks,selectors) for E,_ in next_states):continue
                if dominance:next_states=[(E,w) for E,w in next_states if not D<E]
                if orbit and getattr(orbit,'directed',False):
                    next_states=[(E,w) for E,w in next_states if not orbit(j,front,E,D,banks,selectors)]
                new_word=word|(v<<(selectors[j-1]-1) if j else 0)
                next_states.append((D,new_word))
        states=next_states
        cost['layers'].append(dict(frontier=len(front),candidates=candidates,retained=len(states)))
        cost['highwater']=max(cost['highwater'],len(states))
        if not states:return finish('unsat','no extendible prefix')
        if len(states)>state_cap:return finish('skip','state cap')
    w=states[0][1]
    chosen=list(banks[0][0])
    for j,s in enumerate(selectors,1):chosen+=banks[j][(w>>(s-1))&1]
    x=binary_model(n,chosen)
    if x is None:raise AssertionError('lost retained prefix')
    for s in S:x &= ~(1<<(s-1))
    return finish('sat','raw binary projection',x|w)
