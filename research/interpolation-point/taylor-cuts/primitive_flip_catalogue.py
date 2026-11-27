"""Hereditary physical flip templates from chordless double-cover cycles."""
from collections import defaultdict
import networkx as nx


def build(n,edges,*,cycle_cap=None):
    """Cap counts every emitted double-cover cycle, including nonsimple projections."""
    if cycle_cap is not None and (type(cycle_cap) is not int or cycle_cap<0):
        raise ValueError('invalid output cap')
    bundles=defaultdict(list)
    cover=nx.Graph()
    cover.add_nodes_from(range(2*n))
    for i,(u,v,g) in enumerate(edges):
        if not (0<=u<n and 0<=v<n and u!=v):
            raise ValueError('invalid original edge')
        bundles[tuple(sorted((u,v)))].append(i)
        cover.add_edges_from(((u,v+n),(v,u+n)))
    flips=[]
    for (u,v),ids in bundles.items():
        for i in ids[1:]:
            flips.append(((1<<u)|(1<<v),(ids[0],),(i,)))
    stats=dict(lift_cycles=0,discarded=0,parallel=len(flips),physical_cycles=0,complete=False)
    seen=set()
    for lifted in nx.chordless_cycles(cover):
        stats['lift_cycles']+=1
        if cycle_cap is not None and stats['lift_cycles']>cycle_cap:
            return None,stats
        sites=tuple(v%n for v in lifted)
        if len(set(sites))!=len(sites):
            stats['discarded']+=1
            continue
        ids=tuple(bundles[tuple(sorted((u,v)))][0] for u,v in zip(sites,sites[1:]+sites[:1]))
        key=frozenset(ids)
        if key not in seen:
            seen.add(key)
            flips.append((sum(1<<v for v in sites),ids[::2],ids[1::2]))
    stats['physical_cycles']=len(seen)
    stats['complete']=True
    return tuple(flips),stats
