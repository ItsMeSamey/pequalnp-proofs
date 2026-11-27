"""Exhaust all edge subsets, periods and balanced splits of a four-vertex graph."""
from itertools import combinations
from collections import Counter


def translated(bits,delta,halves):
    for j,(low,high) in enumerate(halves):
        if delta>>j&1:
            stride=1<<j
            bits=((bits&low)<<stride)|((bits&high)>>stride)
    return bits


def check(n):
    edges=list(combinations(range(n),2))
    m=len(edges)
    width=n+m
    assignments=1<<width
    full=(1<<assignments)-1
    cols=[sum(1<<x for x in range(assignments) if x>>i&1) for i in range(width)]
    halves=[(full^c,c) for c in cols]
    clauses=[cols[n+i]^(cols[a]&cols[b]) for i,(a,b) in enumerate(edges)]
    hist=Counter()
    for S in range(1<<m):
        support=(S<<n)
        conjunction=full
        left=right=0
        for j,(a,b) in enumerate(edges):
            uv=(1<<a)|(1<<b)
            if S>>j&1:
                conjunction&=clauses[j]
                support|=uv
                left|=uv
            else:right|=uv
        for shift in range(1<<width):
            assert (translated(conjunction,shift,halves)==conjunction)==(shift&support==0)
        assert conjunction.bit_count()==1<<(width-S.bit_count())
        if m<=3*S.bit_count()<=2*m:
            b=(left&right).bit_count()
            assert b*(b-1)//2>=min(S.bit_count(),m-S.bit_count())
            hist[b]+=1
    print(n,'vertices;',1<<m,'edge subsets;',1<<width,'shifts per subset; balanced boundaries',dict(hist))


if __name__=='__main__':
    for n in (3,4):check(n)
