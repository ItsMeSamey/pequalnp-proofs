"""Original-input checks for four-cap reachability and physical witness recovery."""
from collections import Counter
from itertools import combinations
from random import Random
import networkx as nx

import general_five_cap_host as alg
from common_neighbor_host_check import native,lists,chain


def check(rows,p,q):
    out=alg.find(lists(rows),(p,q))
    yes=native(rows,p,q) is not None
    if out['status']=='UNKNOWN':
        assert max(r.bit_count() for r in rows)>5
    else:
        assert (out['status']=='YES')==yes,(rows,p,q,out,yes)
    if out['witness'] is not None:
        selected=set(out['witness'])
        assert {p,q}<=selected and all(sum(rows[x]>>v&1 for v in selected)%2 for x in selected)
    return out['status']


def deep_template(rounds, kind):
    # Undo paired caps, then a singleton triangle, then either triple.
    g=[{2},{3},{0},{1}]
    p,q=0,1
    forward=[]
    def addsite():
        g.append(set())
        return len(g)-1
    def flip(i,j):
        g[i].symmetric_difference_update({j})
        g[j].symmetric_difference_update({i})
    def record(K,P,Q,U,V,C,childB):
        parentB=tuple(sorted({P,Q}|g[P]|g[Q]))
        forward.append((K,P,Q,U,V,tuple(sorted(C)),parentB,tuple(sorted(childB))))
    for _ in range(rounds):
        childB={p,q}|g[p]|g[q]
        a,b=addsite(),addsite()
        flip(p,q);flip(a,p);flip(b,q)
        record('P',a,b,p,q,(),childB)
        p,q=a,b
    childB={p,q}|g[p]|g[q]
    u,leaf=addsite(),addsite()
    flip(p,q);flip(u,p);flip(u,q);flip(u,leaf)
    record('T',leaf,p,u,q,(),childB)
    q,v=p,leaf
    C=set(g[q])
    childB={q,v}|g[q]|g[v]
    u,p=addsite(),addsite()
    flip(p,u)
    for c in C:
        flip(v,c);flip(u,c)
    if kind=='N':flip(u,v)
    else:flip(u,q);flip(q,v)
    record(kind,p,q,u,v,C,childB)
    assert max(map(len,g))<=5
    return g,(p,q),forward[::-1],{0,1,2,3}


def controls():
    metrics=Counter()
    for kind in ('A','N'):
        g,pins,path,end=deep_template(6,kind)
        rows=[sum(1<<v for v in a) for a in g]
        out=alg.find(lists(rows),pins)
        assert out['status']=='YES' and set(out['witness'])==set(range(len(rows)))
        g,pins,path,end=deep_template(1040,kind)
        root=path[0][6]
        abstract,images,layout=alg.trace_graph(g,pins,root,path,end)
        assert alg.first_conflict(g,abstract,images) is None
        for old_name in (pins if kind=='N' else pins[:1]):
            for late in [i for i in range(len(images)-14,len(images)) if len(g[images[i]])<5]:
                X=images[late]
                if len(g[old_name])>=5:continue
                g[X].add(old_name);g[old_name].add(X)
                fresh,contacts=alg.first_conflict(g,abstract,images)
                result=alg.repair_trace(g,[s.copy() for s in abstract],images,layout,fresh,contacts)
                assert alg.odd(g,result,pins)
                metrics[kind,old_name==pins[1]]+=1
                g[X].remove(old_name);g[old_name].remove(X)
    assert metrics['N',True]>0
    return metrics


if __name__=='__main__':
    statuses=Counter()
    for graph in nx.graph_atlas_g():
        if len(graph)>6:break
        rows=[sum(1<<v for v in graph[i]) for i in graph]
        for p,q in combinations(range(len(rows)),2):
            statuses[check(rows,p,q)]+=1
    rng=Random(154083)
    for n in (7,9,12):
        for _ in range(50):
            graph=nx.gnp_random_graph(n,rng.uniform(.1,.5),seed=rng.randrange(1<<32))
            rows=[sum(1<<v for v in graph[i]) for i in graph]
            statuses[check(rows,*rng.sample(range(n),2))]+=1
    fixture=[22,41,1,2,97,722,176,352,11904,1312,2816,5376,26624,20736,45056,16384]
    for chords in ([],[(10,13)],[(0,11),(0,13),(2,9),(6,10),(10,13)]):
        r=fixture[:]
        for i,j in chords:r[i]^=1<<j;r[j]^=1<<i
        print('review',check(r,15,12))
    print('complete searches',statuses,'triple repairs',controls())
