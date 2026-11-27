"""Compare counts per assignment with a native socket-trace oracle."""
from collections import Counter
from itertools import combinations
from check import compile_open, reaches


def test(n,edges,repetitions):
    clauses=[(-u-1,-v-1) for u,v in edges]*repetitions
    net=compile_open(n,clauses)
    g,succ,_,_,s,t=net
    q=2*len(clauses)
    observed=Counter()
    def trace(x,known,mask):
        h,j=divmod(x,3)
        for b in (0,1):
            if (known>>h)&1 and (mask>>h)&1!=b:continue
            used=known|1<<h
            value=mask|(b<<h)
            out=3*h+(j+b)%3
            if out in succ:
                trace(succ[out],used,value)
            elif out==t:
                # Variable forks occur consecutively in split/merge pairs.
                assignment=sum(((value>>(q+2*i))&1)<<i for i in range(n))
                observed[assignment]+=1<<(g-used.bit_count())
    trace(s,0,0)
    expected={}
    for a in range(1<<n):
        if any((a>>u)&(a>>v)&1 for u,v in edges):continue
        neither=sum(not ((a>>u|a>>v)&1) for u,v in edges)
        expected[a]=4**(repetitions*neither)
    if dict(observed)!=expected:raise AssertionError((edges,repetitions,observed,expected))
    count=sum(observed.values())
    raw=0
    if g<=17:
        raw=1<<g
        if sum(reaches(net,mask) for mask in range(raw))!=count:raise AssertionError('raw')
    if repetitions==n+1 and count%(4**repetitions-1)!=len(expected):raise AssertionError('residue')
    return raw


if __name__=='__main__':
    queries=masks=0
    for n in (2,3,4):
        possible=list(combinations(range(n),2))
        for edge_mask in range(1,1<<len(possible)):
            E=[e for j,e in enumerate(possible) if edge_mask>>(j)&1]
            for r in {1,n+1}:
                # Skip large path trees in the physical oracle.
                if r*len(E)>12:continue
                masks+=test(n,E,r);queries+=1
    print(queries,'physical path-tree histograms;',masks,'raw masks checked')
