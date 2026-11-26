import collections
import itertools
import random
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "subdivision-single-hole"))
from matching_multipole import solve
import networkx as nx

def edge(u,v):
    return tuple(sorted((u,v)))

def matching(g):
    if len(g)==0:
        return frozenset()
    m=nx.max_weight_matching(g,maxcardinality=True)
    return frozenset(edge(*e) for e in m) if 2*len(m)==len(g) else None

def matchings(g):
    if not len(g):
        yield frozenset()
        return
    u=min(g,key=g.degree.__getitem__)
    for v in g[u]:
        for m in matchings(g.subgraph(set(g)-{u,v})):
            yield m|{edge(u,v)}

def reduced(g,forced,forbidden):
    taken=[u for e in forced for u in e]
    if len(set(taken))!=len(taken) or forced&forbidden:
        return None
    h=g.copy()
    h.remove_nodes_from(taken)
    h.remove_edges_from(forbidden)
    return h

def exact(g,pins):
    h=reduced(g,pins,set())
    if h is None:return False
    for m in matchings(h):
        f=g.copy()
        f.remove_edges_from(m|pins)
        if nx.is_bipartite(f):return True
    return False

def dm(g,defects,pins,stats):
    if not defects:
        h=reduced(g,pins,set())
        return h is not None and matching(h) is not None
    assert len(defects)==2
    h=reduced(g,pins|defects,set())
    if h is not None and matching(h) is not None:return True
    h=reduced(g,pins,defects)
    if h is None or matching(h) is None:return False
    allowed=set(pins)
    for u,v in h.edges:
        if matching(h.subgraph(set(h)-{u,v})) is not None:
            allowed.add(edge(u,v))
    a=nx.Graph()
    a.add_nodes_from(g)
    a.add_edges_from(allowed)
    wires={edge(u,v) for u,v in g.edges}-allowed
    skeleton=nx.MultiGraph()
    for e in wires:
        skeleton.add_edge((e,e[0]),(e,e[1]))
    flexible=[]
    for block in nx.connected_components(a):
        ports=[(e,v) for e in sorted(wires) for v in e if v in block]
        if not ports:continue
        if len(ports)>4:
            stats['large']+=1
            return None
        signatures={}
        local=a.subgraph(block)
        samples=[matching(local)]
        if len(ports)==4 and len(block)>2:
            shores=nx.bipartite.color(local)
            ports.sort(key=lambda p:shores[p[1]])
            for colors in [(0,0,0,0),(0,1,0,1),(0,1,1,0)]:
                status,witness=solve(local,[p[1] for p in ports],colors)
                assert status=="SAT",(local.edges,ports,colors,status)
                samples.append(frozenset(edge(*ends) for (ends,key),color in witness.items() if color==2))
        for m in samples:
            f=nx.Graph()
            f.add_nodes_from(block)
            f.add_edges_from(e for e in allowed-m if e[0] in block)
            f.add_edges_from((p,p[1]) for p in ports)
            pairs=[]
            for c in nx.connected_components(f):
                ends=sorted(set(ports)&c)
                if ends:
                    assert len(ends)==2
                    pairs.append(tuple(ends))
            sig=tuple(sorted(pairs))
            signatures[sig]=m
            if len(signatures)>=2:break
        opts=list(signatures)
        if len(ports)==4 and len(block)>2:assert len(opts)==2
        skeleton.add_edges_from(opts[0])
        if len(opts)>1:flexible.append(opts)
        if len(ports)==4 and len(block)>2:
            stats['optional4_'+str(len(opts))]+=1
    d1,d2=sorted(defects)
    initially_together=nx.has_path(skeleton,(d1,d1[0]),(d2,d2[0]))
    for first,second in flexible:
        (p,q),(r,s)=first
        if not nx.has_path(skeleton,p,r):
            skeleton.remove_edges_from(first)
            skeleton.add_edges_from(second)
    d1,d2=sorted(defects)
    # Each step merged complete circuits, so tests for nonconnectivity never become stale.
    same=nx.has_path(skeleton,(d1,d1[0]),(d2,d2[0]))
    stats["skeleton_"+str(initially_together)+"_"+str(same)]+=1
    return same

def examples(n,rng):
    vertices=list(range(n))
    while True:
        perms=[rng.sample(vertices,n) for _ in range(3)]
        if not all(len({p[i] for p in perms})==3 for i in vertices):continue
        g=nx.Graph((i,n+p[i]) for p in perms for i in vertices)
        e1,e2=rng.sample(list(g.edges),2)
        if len(set(e1+e2))<4:continue
        d1=edge(min(e1),min(e2))
        d2=edge(max(e1),max(e2))
        g.remove_edges_from([e1,e2])
        g.add_edges_from([d1,d2])
        if nx.is_connected(g):return g,{d1,d2}

if __name__=='__main__':
    rng=random.Random(8632)
    stats=collections.Counter()
    for n in range(3,9):
        for _ in range(12):
            g,ds=examples(n,rng)
            ed=[edge(*e) for e in g.edges]
            for pins in [ds,*[set(rng.sample(ed,2)) for i in range(20)]]:
                result=dm(g,ds,pins,stats)
                ref=exact(g,pins)
                if result is None:stats['abstain_'+str(ref)]+=1
                else:
                    assert result==ref,(g.edges,ds,pins,result,ref)
                    stats['checked_'+str(ref)]+=1
    for pins in itertools.combinations([edge(*e) for e in nx.complete_bipartite_graph(3,3).edges],2):
        g=nx.complete_bipartite_graph(3,3)
        assert dm(g,set(),set(pins),stats)==exact(g,set(pins))
    print(dict(stats))
