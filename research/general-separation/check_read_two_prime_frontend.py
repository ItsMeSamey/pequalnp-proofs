"""Verify the physical CNF by inclusion-exclusion over its actual clauses."""
from fractions import Fraction
from itertools import product
from math import prod
from read_two_prime_frontend import compile_cnf


def evaluate(instance, p):
    clauses=instance['clauses']
    weights=instance['weights']
    incidences=[[] for _ in weights]
    for i,clause in enumerate(clauses):
        assert 1<=len(clause)<=3 and len(set(clause))==len(clause)
        for v in clause:
            assert 1<=v<=len(weights)
            incidences[v-1].append(i)
    assert all(len(pair)==2 for pair in incidences)
    # A chosen clause is required to fail. A unit-success variable forbids
    # either incident clause from being chosen in the inclusion-exclusion sum.
    blocked={i for w,pair in zip(weights,incidences) if w==1 for i in pair}
    def red(a):
        return a if p is None else a%p
    factors=[((i,),[1,-1]) for i in range(len(clauses)) if i not in blocked]
    for w,pair in zip(weights,incidences):
        scope=tuple(i for i in pair if i not in blocked)
        if scope and w:
            factors.append((scope,[1]+[red(1-w)]*((1<<len(scope))-1)))
    graph={i:set() for i in range(len(clauses)) if i not in blocked}
    for scope,_ in factors:
        for i in scope:
            graph[i].update(set(scope)-{i})
    while graph:
        v=min(graph,key=lambda i:(len(graph[i]),i))
        rest=tuple(sorted(graph.pop(v)))
        assert len(rest)<=8
        for i in rest:
            graph[i].discard(v)
            graph[i].update(set(rest)-{i})
        used=[f for f in factors if v in f[0]]
        factors=[f for f in factors if v not in f[0]]
        positions={i:j for j,i in enumerate((v,)+rest)}
        maps=[([positions[i] for i in scope],table) for scope,table in used]
        tab=[]
        for y in range(1<<len(rest)):
            val=0
            for x in (y*2,y*2+1):
                val+=prod(t[sum(((x>>a)&1)<<j for j,a in enumerate(indices))]
                          for indices,t in maps)
            tab.append(red(val))
        factors.append((rest,tab))
    return red(prod(t[0] for _,t in factors))


def main():
    for p in (5,7,None):
        cases=[(0,[],{}),(0,[()],{}),(1,[(1,-1)],{1:2}),
               (2,[(-1,2,2),(1,)],{1:2,2:-1}),(1,[(1,),(-1,)],{})]
        if p is None:
            cases.append((1,[],{1:Fraction(-3,2)}))
        for n,clauses,selectors in cases:
            raw=compile_cnf(n,clauses,p,selectors=selectors)
            expected=sum(prod(w for i,w in selectors.items() if bits[i-1])
                         for bits in product(range(2),repeat=n)
                         if all(any(bits[abs(l)-1]==int(l>0) for l in c) for c in clauses))
            assert evaluate(raw,p)==(expected if p is None else expected%p)
    print('Physical signed-CNF counts passed over F5, F7, and the rationals.')


if __name__=='__main__':
    main()
