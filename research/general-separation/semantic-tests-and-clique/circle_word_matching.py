"""Exact witness search for prescribed degree parities on a supplied circle word.

solve(word, odd, pins) takes a double-occurrence word with hashable site labels,
a set of prescribed odd sites, and sites required to be selected. Return a set
of labels or None. Uses networkx.max_weight_matching (general graph blossom).
"""
from collections import defaultdict
from itertools import combinations, product
from random import Random
import networkx as nx


def interlaces(occ):
    adj = {v:set() for v in occ}
    for u,v in combinations(occ,2):
        a,b = occ[u]
        c,d = occ[v]
        if (a<c<b) != (a<d<b):
            adj[u].add(v)
            adj[v].add(u)
    return adj


def solve(word, odd=(), pins=()):
    occ = defaultdict(list)
    for i,v in enumerate(word):
        occ[v].append(i)
    odd, pins = set(odd),set(pins)
    if any(len(row)!=2 for row in occ.values()) or not (pins|odd)<=occ.keys():
        raise ValueError("invalid word or unknown pin/parity label")
    if not word:
        return set()
    pinned = [v for v in occ if v in pins]
    adj = interlaces(occ)
    n = len(occ)
    # Port 2*i precedes occurrence i; port 2*i+1 follows it.
    positive = []
    for i,v in enumerate(word):
        invert = i==occ[v][1] and v in odd
        positive.extend((invert,not invert))
    for orientations in product((0,1),repeat=len(pinned)):
        arc_bits = {}
        conflict = False
        for v,before in zip(pinned,orientations):
            # At the second occurrence an even site turns in the opposite direction.
            for i,bit in zip(occ[v],(before,before ^ int(v not in odd))):
                for arc,state in (((i-1)%len(word),bit),(i,1-bit)):
                    if arc in arc_bits and state!=arc_bits[arc]:
                        conflict=True
                    arc_bits[arc]=state
        if conflict:
            continue
        forced = {}
        for arc,state in arc_bits.items():
            for p in (2*arc+1,2*((arc+1)%len(word))):
                forced[p] = bool(state) if positive[p] else not state
        G = nx.Graph()
        G.add_nodes_from(range(6*n))
        for j,(v,indices) in enumerate(occ.items()):
            slots = (4*n+2*j,4*n+2*j+1)
            for i in indices:
                for p in (2*i,2*i+1):
                    if forced.get(p,True):
                        G.add_edges_from((p,slot) for slot in slots)
        for i in range(len(word)):
            a,b = 2*i+1,2*((i+1)%len(word))
            if positive[a]==positive[b]:
                if not forced.get(a,False) and not forced.get(b,False):
                    G.add_edge(a,b)
            else:
                dummy = 6*n+i
                G.add_node(dummy)
                for p in (a,b):
                    if not forced.get(p,False):
                        G.add_edge(dummy,p)
        matching = nx.max_weight_matching(G,maxcardinality=True)
        if 2*len(matching)!=len(G):
            continue
        mate = {}
        for a,b in matching:
            mate[a]=b
            mate[b]=a
        def state(p):
            active = 4*n<=mate[p]<6*n
            return int(active if positive[p] else not active)
        for i in range(len(word)):
            assert state(2*i+1)==state(2*((i+1)%len(word)))
        selected=set()
        for v,(i,j) in occ.items():
            di=state(2*i+1)-state(2*i)
            dj=state(2*j+1)-state(2*j)
            assert di+(-1 if v in odd else 1)*dj==0
            if di:selected.add(v)
        assert pins<=selected and all(len(adj[v]&selected)%2==(v in odd) for v in selected)
        return selected
    return None


def selftest():
    rng=Random(5124)
    count=0
    for n in range(8):
        for _ in range(18):
            word=list(range(n))*2
            rng.shuffle(word)
            sites=set(word)
            pins=set(rng.sample(sorted(sites),min(3,n)))
            odd={v for v in sites if rng.randrange(2)}
            occ={v:[i for i,w in enumerate(word) if w==v] for v in sites}
            adj=interlaces(occ)
            truth=False
            for bits in range(1<<n):
                chosen={i for i in sites if bits>>i&1}
                if pins<=chosen and all(len(adj[v]&chosen)%2==(v in odd) for v in chosen):
                    truth=True
                    break
            assert (solve(word,odd,pins) is not None)==truth
            count+=1
    assert solve('aa',[],['a'])=={'a'}
    assert solve('aa',['a'],['a']) is None
    assert solve('abab','ab','ab')=={'a','b'}
    assert solve('abcbac',[],[]) is not None
    assert solve('abccba','a','a') is None
    # W5 obstruction: each private pentagon plus one opposite-shore mark.
    from high_connectivity_anchor_check import host
    for t in (1,2,3):
        for yes in (False,True):
            G,_,_,m=host(t,yes)
            wheel=G.subgraph([0,1,2,3,4,m])
            assert nx.is_isomorphic(wheel,nx.wheel_graph(6))
    print(count,'seeded exact comparisons, five structured words, six induced W5 controls passed')


if __name__=='__main__':selftest()
