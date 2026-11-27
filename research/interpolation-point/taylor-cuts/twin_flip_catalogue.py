"""Primitive type-cover templates with residual-specific physical representatives."""
from collections import defaultdict
from itertools import combinations,product
import networkx as nx


class Catalogue:
    def __init__(self,n,edges,*,cycle_cap=None):
        if cycle_cap is not None and (type(cycle_cap) is not int or cycle_cap<0):
            raise ValueError('invalid quotient output cap')
        self.complete=False
        bundles=defaultdict(list)
        adj=[set() for _ in range(n)]
        for i,(u,v,g) in enumerate(edges):
            if not 0<=u<n or not 0<=v<n or u==v:
                raise ValueError('invalid edge')
            bundles[tuple(sorted((u,v)))].append(i)
            adj[u].add(v)
            adj[v].add(u)
        self.bundles=bundles
        classes=[]
        for u in range(n):
            for part in classes:
                v=part[0]
                if adj[u]-{v}==adj[v]-{u}:
                    part.append(u)
                    break
            else:
                classes.append([u])
        self.classes=tuple(tuple(c) for c in classes)
        owner={v:i for i,part in enumerate(classes) for v in part}
        q=len(classes)
        cover=nx.Graph()
        cover.add_nodes_from(range(2*q))
        for u,v in bundles:
            a,b=owner[u],owner[v]
            cover.add_edges_from(((a,b+q),(b,a+q)))
        self.stats=dict(types=q,lift_cycles=0,long_patterns=0,repeated_type=0,complete=False)
        self.patterns=[]
        seen=set()
        for cycle in nx.chordless_cycles(cover):
            self.stats['lift_cycles']+=1
            if cycle_cap is not None and self.stats['lift_cycles']>cycle_cap:
                return
            if len(cycle)<6:
                continue
            types=tuple(i%q for i in cycle)
            if any(types.count(j)>len(classes[j]) for j in set(types)):
                continue
            key=min(seq[k:]+seq[:k] for seq in (types,types[::-1]) for k in range(len(types)))
            if key not in seen:
                seen.add(key)
                self.patterns.append(key)
                self.stats['repeated_type']+=int(len(set(key))!=len(key))
        self.short=[]
        for p,ids in bundles.items():
            mask=sum(1<<v for v in p)
            for i in ids[1:]:
                self.short.append((mask,(ids[0],),(i,)))
        by_sites=defaultdict(list)
        for p,r in combinations(bundles,2):
            if set(p).isdisjoint(r):
                by_sites[tuple(sorted(p+r))].append((p,r))
        for sites,alternatives in by_sites.items():
            mask=sum(1<<v for v in sites)
            for (p,r),(s,t) in combinations(alternatives,2):
                for i,j,k,l in product(bundles[p],bundles[r],bundles[s],bundles[t]):
                    self.short.append((mask,(i,j),(k,l)))
        self.complete=True
        self.stats.update(complete=True,long_patterns=len(self.patterns),physical_short=len(self.short))

    def flips(self,mask):
        if not self.complete:
            raise ValueError('unfinished catalogue')
        for item in self.short:
            if item[0]&mask==item[0]:
                yield item
        for pattern in self.patterns:
            available={j:iter(v for v in self.classes[j] if mask>>v&1) for j in set(pattern)}
            sites=[next(available[j],None) for j in pattern]
            if None in sites:
                continue
            ids=tuple(self.bundles[tuple(sorted((u,v)))][0] for u,v in zip(sites,sites[1:]+sites[:1]))
            yield sum(1<<v for v in sites),ids[::2],ids[1::2]
