"""Independent subset oracle and locally accepted, physically chorded long walks."""
from collections import Counter
from itertools import combinations
from random import Random
import networkx as nx
import common_neighbor_host_solver as impl
from degree_five_periodic_prime import chain


def native(rows,p,q):
    return next((s for s in range(1<<len(rows)) if s>>p&1 and s>>q&1 and all(
        (s&r).bit_count()%2 for i,r in enumerate(rows) if s>>i&1)),None)


def lists(rows):
    return [[v for v in range(len(rows)) if r>>v&1] for r in rows]


def compare(rows,p,q):
    g=lists(rows)
    out=impl.find(g,[p,q])
    word=native(rows,p,q)
    if out['status']=='UNKNOWN':
        assert not impl.promised([set(row) for row in g])
    else:
        assert (out['status']=='YES') == (word is not None)
    if out['witness'] is not None:
        s=sum(1<<j for j in out['witness'])
        assert all((r&s).bit_count()%2 for j,r in enumerate(rows) if s>>j&1)
    return out['status']


def remote():
    rows,p,q=chain(80)
    g=[set(row) for row in lists(rows)]
    records=[]
    for i in reversed(range(80)):
        c=4+4*i
        old=(0,1) if i==0 else (c-2,c-1)
        s,t=old
        records.extend([('P',c+2,c+3,c+1,s),('T',c+1,s,c,t)])
    end={0,1,2,3}
    base,image,caps=impl.materialize(g,(p,q),records,end)
    assert impl.first_conflict(g,base,image) is None
    counts=Counter()
    # Four endpoints after 128 layers are far enough to escape the rolling window.
    for level in (0,1):
        c=caps[level]
        for old in c[5]:
            for x in range(280,len(image)):
                if len(g[image[x]])==5 or len(g[image[old]])==5:continue
                if not any(y<x for y in base[x]):continue
                a,b=image[x],image[old]
                g[a].add(b);g[b].add(a)
                if impl.promised(g):
                    pos,contacts=impl.first_conflict(g,base,image)
                    w=impl.repair(g,base,image,caps,pos,contacts)
                    assert impl.odd(g,w,(p,q))
                    counts[(c[0],old==c[1])]+=1
                g[a].remove(b);g[b].remove(a)
    # Chords from the same late site to multiple old names exercise the claw and
    # path branches; step two also requires true reverse lifting of earlier caps.
    for level in (0,1,2,3):
        kind,p0,q0,u0,v0,gone,_=caps[level]
        for old in ((p0,q0),(u0,q0)) if kind=='T' else ((p0,q0),):
            for x in range(280,len(image)):
                labels=[image[h] for h in old]
                X=image[x]
                if len(g[X])+2>5 or any(len(g[a])==5 for a in labels):continue
                for a in labels:g[a].add(X);g[X].add(a)
                if impl.promised(g):
                    pos,contacts=impl.first_conflict(g,base,image)
                    w=impl.repair(g,base,image,caps,pos,contacts)
                    assert impl.odd(g,w,(p,q))
                    counts['two chords',level]+=1
                for a in labels:g[a].remove(X);g[X].remove(a)
    # Identify distant template leaves physically. The earlier neighbor of the
    # second occurrence produces a fresh chord before the duplicate is read.
    late=image.index(2)
    for first in (p,q):
        merged=[set(v) for v in g]
        for j in list(merged[2]):
            merged[j].remove(2);merged[j].add(first);merged[first].add(j)
        merged[2].clear()
        labels=[first if name==2 else name for name in image]
        pos,contacts=impl.first_conflict(merged,base,labels)
        assert pos<late and impl.promised(merged)
        w=impl.repair(merged,base,labels,caps,pos,contacts)
        assert impl.odd(merged,w,(p,q))
        counts['remote repeat',0]+=1
    assert len(counts)>=3
    return counts


if __name__=='__main__':
    status=Counter()
    for g in nx.graph_atlas_g():
        if len(g)>5:break
        rows=[sum(1<<v for v in g[u]) for u in g]
        for p,q in combinations(range(len(g)),2):status[compare(rows,p,q)]+=1
    rng=Random(498272)
    for n in (6,8,10):
        for _ in range(30):
            g=nx.gnp_random_graph(n,rng.uniform(.15,.55),seed=rng.randrange(1<<32))
            rows=[sum(1<<v for v in g[u]) for u in g]
            p,q=rng.sample(range(n),2)
            status[compare(rows,p,q)]+=1
    for periods in (2,4,8):
        rows,p,q=chain(periods)
        out=impl.find(lists(rows),(p,q))
        assert out['status']=='YES' and len(out['witness'])==len(rows)
    # Source: review-width7/{counterexample,single-chord-no}.json.
    fixture=[22,41,1,2,97,722,176,352,11904,1312,2816,5376,26624,20736,45056,16384]
    print('review base',compare(fixture,15,12))
    for chords in ([(10,13)],[(0,11),(0,13),(2,9),(6,10),(10,13)]):
        aug=fixture[:]
        for i,j in chords:aug[i]^=1<<j;aug[j]^=1<<i
        assert native(aug,15,12) is None
        print('review augmentation',compare(aug,15,12))
    print('subset comparisons' ,status,'remote repairs',remote())
