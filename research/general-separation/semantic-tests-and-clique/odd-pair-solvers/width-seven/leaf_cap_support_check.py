"""Direct support and neighborhood tests for the three leaf/high cap reductions."""
from collections import Counter
from itertools import combinations
import networkx as nx
from single_leaf_high_pin_check import odd


def bits(x):
    return [i for i in range(x.bit_length()) if x >> i & 1]


def reduce(rows,p,q):
    u,=bits(rows[p])
    if u==q:
        return None
    r=list(rows)
    def flip(i,j):
        r[i]^=1<<j
        r[j]^=1<<i
    if rows[q].bit_count()==1:
        v,=bits(rows[q])
        if u==v or not rows[u]>>v&1:
            return None
        flip(u,v)
        child=(u,v)
        removed=(p,q)
        kind='paired'
    else:
        removed=(p,u)
        if rows[u]>>q&1:
            common=rows[u]&rows[q]
            exclusive=rows[q]&~((1<<u)|common)
            if rows[u]!=((1<<p)|(1<<q)|common):return None
            if common.bit_count()==1:
                v,=bits(common)
                kind='common'
            elif common.bit_count()==3 and exclusive.bit_count()==1:
                v,=bits(exclusive)
                for j in bits(common):flip(v,j)
                kind='exclusive'
            else:return None
            flip(q,v)
        else:
            common=rows[q]
            extra=rows[u]&~((1<<p)|common)
            if common.bit_count()!=3 or extra.bit_count()!=1 or common&~rows[u]:return None
            v,=bits(extra)
            for j in bits(common):flip(v,j)
            kind='nonadjacent'
        child=(q,v)
    gone=sum(1<<i for i in removed)
    r=[0 if gone>>i&1 else mask&~gone for i,mask in enumerate(r)]
    return kind,child,gone,r


def verify(rows,p,q,counts):
    pins=(1<<p)|(1<<q)
    full=(1<<len(rows))-1
    orig={w for w in range(1<<len(rows)) if w&pins==pins and odd(rows,w)}
    out=reduce(rows,p,q)
    if out is None:
        if orig=={full}:
            assert len(rows)<=4
        return
    kind,(a,b),gone,rr=out
    child=(1<<a)|(1<<b)
    words={w|gone for w in range(1<<len(rows)) if not(w&gone) and w&child==child and odd(rr,w)}
    assert orig==words
    assert not (pins|rows[p]|rows[q]) & ~(gone|child|rr[a]|rr[b])
    counts[kind,orig=={full}]+=1


def main():
    counts=Counter()
    for g in nx.graph_atlas_g():
        if not len(g) or not nx.is_connected(g):continue
        rows=[sum(1<<j for j in g[i]) for i in g]
        if any(r.bit_count() not in (1,3,5) for r in rows):continue
        for p in g:
            if rows[p].bit_count()==1:
                for q in g:
                    if q!=p:verify(rows,p,q,counts)
    # Enumerate the varying edges among all nonroot cap sites. The theorem's
    # bijection holds even if a site there has even degree in the full graph.
    for case in ('nonadjacent','common','exclusive'):
        for extra_site in (False,True):
            n=(7 if case!='common' else 5)+extra_site
            rows=[0]*n
            def edge(i,j):
                rows[i]^=1<<j
                rows[j]^=1<<i
            edge(0,1)
            if case=='nonadjacent':
                for j in (3,4,5):edge(1,j);edge(2,j)
                edge(1,6)
            else:
                edge(1,2)
                C=(3,) if case=='common' else (3,4,5)
                for j in C:edge(1,j);edge(2,j)
                edge(2,4 if case=='common' else 6)
            slots=list(combinations(range(3,n),2))
            for code in range(1<<len(slots)):
                if code:
                    mask=code&-code
                    edge(*slots[mask.bit_length()-1])
                verify(rows,0,2,counts)
    print(sorted(counts.items()))
if __name__=='__main__':main()
