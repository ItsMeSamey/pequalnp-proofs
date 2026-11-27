"""Original CNF decision by one actual prefix per verified suffix syndrome."""
from itertools import combinations
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'selector-proxy-native'))
from proxy import recode,accepts_cnf
from prefix import binary_model
from coset import kernel,tail_equations,insert,parity


class WorkLimit(Exception):
    pass


def bit(v):
    return 1<<(v-1)


def physical_checks(n,front,remaining,fixed):
    lifts=kernel(n,tail_equations(remaining,fixed=fixed))
    project=[sum(parity(w&bit(v))<<i for i,v in enumerate(front)) for w in lifts]
    orth=kernel(len(front),project)
    checks=tuple(sum(bit(v) for i,v in enumerate(front) if mask>>i&1) for mask in orth)
    return checks


def translated_implications(rows,base):
    """Zero satisfies the translated formula. Extract positive implications."""
    edges={};negative=[]
    for row in rows:
        shifted=tuple(-l if base&bit(abs(l)) else l for l in row)
        pos=[l for l in shifted if l>0];neg=[-l for l in shifted if l<0]
        if not neg:raise AssertionError('invalid zero baseline')
        if pos:edges.setdefault(neg[0],set()).add(pos[0])
        else:negative.append(sum(bit(v) for v in set(neg)))
    return edges,negative


def oracle(n,arm,oldfront,oldword,rows,target,cost,limits):
    if cost['oracle_calls']>=limits[0]:raise WorkLimit('oracle call cap')
    cost['oracle_calls']+=1
    pins=[(v if oldword&bit(v) else -v,) for v in oldfront]
    fixedmask=sum(bit(v) for v in oldfront)
    # Compress parity constraints after pinning, including their RHS.
    table={}
    for j,row in enumerate(rows):
        rest,rhs=insert(table,row&~fixedmask,((target>>j)&1)^parity(row&oldword&fixedmask))
        if not rest and rhs:return None
    constraints=tuple(table.values())
    binary=list(arm)+pins
    base=binary_model(n,binary)
    if base is None:return None
    needed=sum((rhs^parity(row&base))<<j for j,(row,rhs) in enumerate(constraints))
    if needed==0:return base
    edges,negative=translated_implications(binary,base)
    # Include every active binary/parity variable, then collapse equal principal
    # closures. Equal closures are exactly one SCC. Unobserved variables are free.
    active={abs(l) for r in binary for l in r}
    for row,_ in constraints:
        while row:
            b=row&-row;active.add(b.bit_length());row^=b
    closures={}
    for v in sorted(active):
        if v in closures:continue
        reach={v};stack=[v]
        while stack:
            for u in edges.get(stack.pop(),()):
                if u not in reach:reach.add(u);stack.append(u)
        closures[v]=sum(bit(u) for u in reach)
    seeds=tuple(sorted(set(closures.values())))
    for h in range(1,min(len(constraints),len(seeds))+1):
        for subset in combinations(seeds,h):
            if cost['seed_subsets']>=limits[1]:raise WorkLimit('closure seed cap')
            cost['seed_subsets']+=1
            mask=0
            for u in subset:mask|=u
            if any(mask&bad==bad for bad in negative):continue
            if all(parity(row&(base^mask))==rhs for row,rhs in constraints):
                return base^mask
    return None


def solve_cnf(n,clauses,*,codim_cap=3,oracle_call_cap=100000,closure_seed_cap=1000000):
    limits=(oracle_call_cap,closure_seed_cap)
    if any(type(x) is not int or x<0 for x in (codim_cap,)+limits):
        raise ValueError('caps must be nonnegative integers')
    raw=tuple(tuple(c) for c in clauses);chart=recode(n,raw)
    if chart is None:return dict(status='skip',reason='normalized source width')
    rec,orig,data,masters,copies=chart;N=n+len(copies)
    selectors=tuple(orig[v] for v in masters);idx={s:i+1 for i,s in enumerate(selectors)}
    banks=[[[],[]] for _ in range(len(selectors)+1)];physical=[[] for _ in banks]
    for row in rec:
        guard=[l for l in row if abs(l) in idx]
        if len(guard)>1:raise AssertionError('unexpected chart')
        j=idx[abs(guard[0])] if guard else 0
        banks[j][int(bool(guard and guard[0]<0))].append(tuple(l for l in row if l not in guard))
        physical[j].append(row)
    scopes=[{abs(l) for arm in bank for r in arm for l in r} for bank in banks]
    tails=[set() for _ in banks]
    for j in reversed(range(len(banks)-1)):tails[j]=tails[j+1]|scopes[j+1]
    seen=set();plans=[];cost=dict(cuts=[],oracle_calls=0,seed_subsets=0,retained=[],
                                  raw_names=n,physical_names=N,raw_clauses=len(raw),
                                  physical_clauses=len(rec),limits=[codim_cap,*limits])
    for j,scope in enumerate(scopes):
        newmask=sum(bit(v) for v in scope-seen)
        seen|=scope
        front=tuple(sorted(seen&tails[j]))
        H=physical_checks(N,front,(r for group in physical[j+1:] for r in group),selectors[:j])
        cost['cuts'].append(dict(frontier=len(front),d=len(H)))
        if len(H)>codim_cap:return dict(status='skip',reason='tail codimension cap',cost=cost)
        plans.append((newmask,front,H))
    oldfront=();states={0:0}
    try:
        for j,(newmask,front,H) in enumerate(plans):
            fresh={}
            for word in states.values():
                for val,arm in enumerate(banks[j] if j else banks[j][:1]):
                    for syndrome in range(1<<len(H)):
                        if syndrome in fresh:continue
                        x=oracle(N,arm,oldfront,word,H,syndrome,cost,limits)
                        if x is None:continue
                        extension=word|(x&newmask)
                        if j and val:extension|=bit(selectors[j-1])
                        if any(parity(r&extension)!=((syndrome>>i)&1) for i,r in enumerate(H)):
                            raise AssertionError('boundary gluing mismatch')
                        fresh[syndrome]=extension
                    if len(fresh)==1<<len(H):break
                if len(fresh)==1<<len(H):break
            states=fresh;oldfront=front;cost['retained'].append(len(states))
            if not states:return dict(status='unsat',cost=cost)
    except WorkLimit as exc:return dict(status='skip',reason=str(exc),cost=cost)
    y=next(iter(states.values()))
    if not accepts_cnf(rec,y):raise AssertionError('recoded witness failed')
    x=sum(parity(y&bit(q))<< (v-1) for v,q in orig.items())
    if not accepts_cnf(raw,x):raise AssertionError('source witness failed')
    return dict(status='sat',witness=x,cost=cost)
