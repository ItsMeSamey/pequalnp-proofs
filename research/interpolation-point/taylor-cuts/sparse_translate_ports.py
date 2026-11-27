"""Deterministic scalar GF(3) matching search on supplied port modules."""
from collections import deque
from fractions import Fraction
from itertools import combinations
import networkx as nx
from labelled_switching_generators import linear


def binary(equations):
    piv={}
    for mask,rhs in equations:
        while mask:
            p=mask.bit_length()-1
            if p not in piv:
                piv[p]=(mask,rhs)
                break
            m,b=piv[p]
            mask^=m
            rhs^=b
        else:
            if rhs:
                return None
    return piv


def parametrise(n,eq):
    piv=binary(eq)
    if piv is None:
        return None
    free=[i for i in range(n) if i not in piv]
    forms={v:(1<<j,0) for j,v in enumerate(free)}
    for p,(m,b) in sorted(piv.items()):
        s=0
        for j in range(p):
            if m>>j&1:
                k,c=forms[j]
                s^=k
                b^=c
        forms[p]=(s,b)
    return [forms[i] for i in range(n)],len(free)


def solve(n,edges,modules,target,*,potentials=None,subset_cap=None):
    """Original edges are (u,v,integer gain mod 3); module vertices partition range(n)."""
    if n<0 or target not in (0,1,2) or subset_cap is not None and subset_cap<0:
        raise ValueError('invalid dimensions, target or budget')
    edges=tuple((u,v,g%3) for u,v,g in edges)
    modules=tuple(tuple(sorted(M)) for M in modules)
    if any(not M for M in modules) or sorted(v for M in modules for v in M)!=list(range(n)):
        raise ValueError('invalid partition')
    owner={v:j for j,M in enumerate(modules) for v in M}
    gs=[nx.Graph() for M in modules]
    for graph,M in zip(gs,modules):
        graph.add_nodes_from(M)
    internal=[[] for M in modules]
    ports={}
    links=[]
    for i,(u,v,g) in enumerate(edges):
        if not(0<=u<n and 0<=v<n and u!=v):
            raise ValueError('invalid edge')
        if owner[u]==owner[v]:
            j=owner[u]
            gs[j].add_edge(u,v,idx=i)
            internal[j].append(i)
        else:
            if u in ports or v in ports:
                raise ValueError('a port has multiple intermodule edges')
            ports[u]=ports[v]=len(links)
            links.append(i)
    stats=dict(tested_subsets=0)
    if potentials is None:
        potentials=[0]*n
        for M,ids in zip(modules,internal):
            fit=linear(len(M),[([int(x in edges[i][:2]) for x in M],edges[i][2]) for i in ids])
            if fit is None:
                return 'UNKNOWN',None,{**stats,'reason':'internal endpoint fit unavailable'}
            for x,c in zip(M,fit[0]):
                potentials[x]=c
    else:
        potentials=tuple(potentials)
        if len(potentials)!=n or any((potentials[edges[i][0]]+potentials[edges[i][1]])%3!=edges[i][2]
                                     for ids in internal for i in ids):
            raise ValueError('invalid endpoint potentials')
    code=parametrise(len(links),[(sum(1<<ports[v] for v in M if v in ports),len(M)%2) for M in modules])
    if code is None:
        return 'UNSAT',None,{**stats,'reason':'inconsistent port code'}
    forms,r=code
    stats['rank']=r
    coeff={0:sum(potentials)-target}
    for i,(s,c) in zip(links,forms):
        u,v,g=edges[i]
        a=(g-potentials[u]-potentials[v])*2
        coeff[0]=coeff.get(0,0)+a
        coeff[s]=coeff.get(s,0)-a*(-1)**c
    coeff={s:c%3 for s,c in coeff.items() if c%3}
    P={0:1}
    for i,a in coeff.items():
        for j,b in coeff.items():
            P[i^j]=P.get(i^j,0)-a*b
    P={s:c%3 for s,c in P.items() if c%3}
    D=len(P)
    stats['support']=D
    if not D:
        return 'UNSAT',None,stats
    def match(j,V):
        graph=gs[j].subgraph(V)
        m=nx.max_weight_matching(graph,maxcardinality=True)
        if 2*len(m)==len(V):
            return tuple(graph[u][v]['idx'] for u,v in m)
        return None
    events=[]
    for j,M in enumerate(modules):
        mandatory=set(M)-ports.keys()
        pv=sorted(set(M)-mandatory)
        h=max(len(M)-1-gs[j].degree(v) for v in M)
        for count in range(len(mandatory)%2,min(len(pv),2*h+1-len(mandatory))+1,2):
            for S in combinations(pv,count):
                if subset_cap is not None and stats['tested_subsets']>=subset_cap:
                    return 'UNKNOWN',None,{**stats,'reason':'subset cap'}
                stats['tested_subsets']+=1
                V=mandatory|set(S)
                if match(j,V) is not None:
                    continue
                eq=[(forms[ports[v]][0],forms[ports[v]][1]^int(v not in V)) for v in pv]
                piv=binary(eq)
                if piv is not None:
                    events.append(tuple(piv.values()))
    delta=sum((Fraction(1,1<<len(event)) for event in events),Fraction())
    stats.update(events=len(events),delta=str(delta))
    if D*delta>=1:
        return 'UNKNOWN',None,{**stats,'reason':'density bound'}
    shift_rows={}
    shifts=[]
    todo=deque([0])
    frequencies=tuple(P)
    while todo:
        z=todo.popleft()
        row=[P[i]*(-1 if (i&z).bit_count()%2 else 1)%3 for i in frequencies]
        for p,basis in sorted(shift_rows.items()):
            c=row[p]
            row=[(a-c*b)%3 for a,b in zip(row,basis)]
        if not any(row):
            continue
        p=next(i for i,c in enumerate(row) if c)
        shift_rows[p]=tuple(c*row[p]%3 for c in row)
        shifts.append(z)
        todo.extend(z^(1<<i) for i in range(r))
    translated=[tuple((m,b^((m&t).bit_count()%2)) for m,b in event) for event in events for t in shifts]
    def cost(k,z):
        fixed=(1<<k)-1
        total=Fraction()
        for event in translated:
            piv=binary((m&~fixed,b^((m&z).bit_count()%2)) for m,b in event)
            if piv is not None:
                total+=Fraction(1,1<<len(piv))
        return total
    z=0
    for k in range(r):
        trial=z|(1<<k)
        if cost(k+1,trial)<cost(k+1,z):
            z=trial
    if cost(r,z)!=0:
        raise ArithmeticError('conditional expectation failed')
    z=next(z^t for t in shifts if sum(c*(-1 if ((z^t)&i).bit_count()%2 else 1) for i,c in P.items())%3)
    selected=[i for i,(s,c) in zip(links,forms) if c^((s&z).bit_count()%2)]
    used={v for i in selected for v in edges[i][:2]}
    for j,M in enumerate(modules):
        w=match(j,set(M)-used)
        if w is None:
            raise ArithmeticError('uncovered infeasible port pattern')
        selected.extend(w)
    if sorted(v for i in selected for v in edges[i][:2])!=list(range(n)) or sum(edges[i][2] for i in selected)%3!=target:
        raise ArithmeticError('original edge gain or coverage failed')
    return 'SAT',tuple(selected),stats


if __name__=='__main__':
    import json,sys
    data=json.load(sys.stdin)
    status,witness,metrics=solve(**data)
    print(json.dumps(dict(status=status,witness=witness,metrics=metrics)))
