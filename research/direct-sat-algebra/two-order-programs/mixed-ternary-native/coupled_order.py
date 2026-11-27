"""Label-independent discovery of the coupled parity-helper presentation."""
from collections import defaultdict
from time import perf_counter_ns
from solver import solve as solve_chart, accepts_cnf,parity


def infer(n,raw):
    tables=defaultdict(set)
    for row in raw:
        literals=set(row)
        if any(-l in literals for l in literals):continue
        if len(literals)>3:return None
        if len(literals)!=3:continue
        scope=tuple(sorted(abs(l)-1 for l in literals))
        tables[scope].add(sum((-(i+1) in literals)<<j for j,i in enumerate(scope)))
    parity_scopes=[];main=[]
    for s,forbid in tables.items():
        if len(forbid)==4 and len({parity(x) for x in forbid})==1:parity_scopes.append(set(s))
        elif len(forbid)==1:main.append(set(s))
        else:return None
    active=set().union(*main)
    if len(main)<2 or len(active)!=3*len(main):return None
    owner={v:i for i,S in enumerate(main) for v in S}
    pairs={};singles={}
    for s in parity_scopes:
        common=s&active
        if len(common) not in (1,2):return None
        owners={owner[v] for v in common}
        if len(owners)!=1:return None
        i=next(iter(owners));book=pairs if len(common)==2 else singles
        if i in book:return None
        book[i]=(common,s-active)
    core=set();helpers=set();anchors=set()
    for i,S in enumerate(main):
        if i not in pairs or i not in singles:return None
        ab,d=pairs[i];c,hd=singles[i]
        if ab|c!=S or not d<=hd:return None
        core.update(ab);helpers.update(c|d);anchors.update(hd-d)
    if len(anchors)!=1 or len(helpers)!=2*len(main) or (core|anchors)&helpers:return None
    for row in raw:
        c=set(row)
        if len(c)<=2 and not any(-l in c for l in c) and any(abs(l)-1 in helpers for l in c):return None
    return sorted(anchors)+sorted(set(range(n))-helpers-anchors)+sorted(helpers)


def solve(n,clauses,**options):
    start=perf_counter_ns()
    if type(n) is not int or n<0:raise ValueError('invalid raw dimension')
    raw=tuple(tuple(c) for c in clauses)
    if any(type(l) is not int or not 1<=abs(l)<=n for c in raw for l in c):raise ValueError('invalid literal')
    if 'extract_arities' in options:raise ValueError('automatic route selects extraction arities')
    permutation=infer(n,raw)
    if permutation is None:
        result=solve_chart(n,raw,**options)
    else:
        index={v:i+1 for i,v in enumerate(permutation)}
        remapped=[tuple(index[abs(l)-1]*(1 if l>0 else -1) for l in c) for c in raw]
        result=solve_chart(n,remapped,extract_arities=(3,),**options)
        if result['status']=='sat':
            x=result['witness']
            result['witness']=sum(((x>>i)&1)<<v for i,v in enumerate(permutation))
    if result['status']=='sat' and not accepts_cnf(raw,result['witness']):
        raise AssertionError('untouched CNF replay failed')
    result['cost']['inferred_order']=permutation
    result['cost']['original_total_elapsed_ns']=perf_counter_ns()-start
    return result
