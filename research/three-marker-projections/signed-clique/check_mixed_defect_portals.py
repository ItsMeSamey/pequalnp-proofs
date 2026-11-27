"""Capped indexed replay of mixed L and localized portal gains on K8."""
from itertools import combinations
from random import Random
from component_nullity import bits, dependencies, trace
from thick_tag_solver import basis, combine
from omega_signature_cover import signatures, dot, _linear


def span(values):
    _,ids=basis(values)
    return {combine([values[j] for j in ids],x) for x in range(1<<len(ids))}


def path(start,end,edges,allowed):
    pred={start:None}
    todo=[start]
    while todo:
        u=todo.pop()
        if u==end:
            word=0
            while pred[u] is not None:
                u,j=pred[u]
                word ^= 1<<j
            return word
        for j in allowed:
            a,b=edges[j]
            if u==a or u==b:
                v=a^b^u
                if v not in pred:
                    pred[v]=(u,j)
                    todo.append(v)
    raise AssertionError("missing literal portal-to-root path")


def check(k, projected, seed):
    n=8
    edges=list(combinations(range(n),2))
    Random(seed).shuffle(edges)
    N=len(edges)
    T=span(projected)
    perp={g for g in range(1<<k) if all(not dot(g,s) for s in projected)}
    t=len(projected)
    project=lambda g:sum(dot(g,s)<<j for j,s in enumerate(projected))
    imageL={0,project(1)}  # genuine global L=<1>; P={0}
    if projected==[1]:
        X=[0,1,0,1,0,1,0,1]
    elif projected==[1,2]:
        X=[0,1,0,1,0,3,2,3]
    else:
        X=[0,0,0,0,1,1,2,2]
    def coset(v):
        return min(X[v]^p for p in imageL)
    labels=[]
    for a,b in edges:
        if a==0:
            val=next(g for g in range(1<<k) if project(g)==X[b])
            if b==2 and (perp-{0,1}):
                val ^= min(perp-{0,1})
        else:
            val=((X[a]^X[b])&1) if project(1) else 0
            # The 123 triangle has odd L gain. In the last case the triangle
            # is an inactive rooted cycle; in the first cases it is not.
            if (a,b)==(2,3):
                val ^= 1
        labels.append(val)
    cuts=[sum(1<<j for j,e in enumerate(edges) if v in e) for v in range(n)]
    defects=signatures(labels,k)
    D=cuts[1:]+defects
    assert len(basis(D)[1])==n-1+k
    assert {labels[j] for j,(a,b) in enumerate(edges) if a}=={0,1}
    pre=lambda g:combine(defects,g)
    words=[pre(s)^combine(cuts,sum(((v>>j)&1)<<i for i,v in enumerate(X)))
           for j,s in enumerate(projected)]
    S=0
    for word in words:
        S|=word
    U=list(bits(((1<<N)-1)^S))
    assert all(project(labels[j])==X[a]^X[b] for j in U for a,b in [edges[j]])
    # Build the actual finite skeleton including distinct full-label portals;
    # realize each of its arcs as an original-index walk via its bin root.
    bins={coset(v) for v in range(1,n)}
    root={c:min(v for v in range(1,n) if coset(v)==c) for c in bins}
    portals={}
    for j in U:
        a,b=edges[j]
        if a==0:
            portals.setdefault((coset(b),labels[j]),(j,b))
    sk_edges=[]
    walks=[]
    for (c,d),(j,b) in portals.items():
        internal=[i for i in U if edges[i][0] and all(coset(v)==c for v in edges[i])]
        route=path(b,root[c],edges,internal)^(1<<j)
        assert combine(labels,route)>>1==d>>1 and not route&S
        sk_edges.append((1<<0)^(1<<root[c]))
        walks.append(route)
    assert len(basis(sk_edges)[1])==len(bins)
    realized=[]
    inc=[(1<<a)^(1<<b) for a,b in edges]
    for cycle in dependencies(sk_edges):
        closed=combine(walks,cycle)
        assert not combine(inc,closed) and not closed&S
        realized.append(combine(labels,closed))
    assert {g>>1 for g in span(realized)}=={g>>1 for g in perp}
    if 1 in perp:
        cycle=sum(1<<edges.index(e) for e in combinations((1,2,3),2))
        assert not cycle&S and not combine(inc,cycle) and combine(labels,cycle)==1
        realized.append(1)
    assert span(realized)==perp
    for v in range(1,n):
        path(0,v,edges,U)
    actual_T={s for s in range(1<<k) if any(not (pre(s)^cut)&~S for cut in span(cuts))}
    assert actual_T==T
    # Physical q and named rows, with independent named coordinates on the
    # designated translations; replay the complete span on literal edge IDs.
    q=signatures(dependencies(signatures(D,N)),N)
    namedrows=[_linear([(w,int(i==j)) for j,w in enumerate(words)],N)[0] for i in range(t)]
    named=signatures(namedrows,N)
    assert trace(q,named,S)==frozenset(range(1<<t))
    assert all(not combine(q,w) and combine(named,w)==1<<j for j,w in enumerate(words))
    allowed=[w for w in span(D) if not w&~S]
    assert set(allowed)==span(words)
    return len(bins),len(portals),len(realized)


if __name__=="__main__":
    for k,proj in [(2,[1]),(3,[1,2]),(3,[2,4])]:
        stats=check(k,proj,47+k)
        print("k, t, bins, portal triples, cycle generators:",k,len(proj),*stats)
