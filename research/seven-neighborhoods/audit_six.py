import itertools
import networkx as nx
from role_general import possibilities

def gs():
 atlas=[g for g in nx.graph_atlas_g() if 1<=g.number_of_edges()<=6 and nx.is_connected(g)]
 def build(j,stack,v,e):
    if e==6:yield nx.disjoint_union_all(stack);return
    for t in range(j,len(atlas)):
        g=atlas[t];x=g.number_of_nodes();y=g.number_of_edges()
        if e+y<=6 and v+x<=8:yield from build(t,stack+[g],v+x,e+y)
 yield from build(0,[],0,0)

def verify(ns):
 L=[{(i+d)%13 for d in (0,1,3,9)} for i in ns];whole=set.union(*L);K=range(6)
 inc=sorted(sum(1<<t for t in K if p in L[t]) for p in range(13))
 aut=[h for h in itertools.permutations(K) if sorted(sum(1<<h[t] for t in K if p in L[t]) for p in range(13))==inc]
 def key(S,G):
    vv=max(max(e) for e in G.values())+1
    return min((tuple(sorted(h[t] for t in S)),tuple(sorted(tuple(sorted(h[t] for t in K if i in G[t])) for i in range(vv)))) for h in aut)
 wanted={key(S,G):len(dd) for S,G,_,_,dd in possibilities(ns,17)}
 found={};exam=set()
 for graph in gs():
    E=list(graph.edges());v=graph.number_of_nodes();eix={frozenset(p):i for i,p in enumerate(E)}
    sym={tuple(eix[frozenset((g[a],g[b]))] for a,b in E) for g in nx.algorithms.isomorphism.GraphMatcher(graph,graph).isomorphisms_iter()}
    visited=set()
    for perm in itertools.permutations(K):
        if perm in visited:continue
        for h in aut:
            visited.update(tuple(h[perm[j]] for j in p) for p in sym)
        G={t:e for t,e in zip(perm,E)}
        for S in [()]+[(t,) for t in K]:
            r=len(S)
            if 11-r-v<(2 if r else 3):continue
            z=key(S,G)
            if z in exam:continue
            exam.add(z);count=0
            for choices in itertools.product(*(L[t] for t in S)):
                C=[t.copy() for t in L]
                for t,p in zip(S,choices):C[t].remove(p)
                lo=[set.union(*(C[t] for t,e in G.items() if i in e)) for i in range(v)]
                if any(b==whole for b in lo) or any(lo[a]&lo[b]!=C[t] for t,(a,b) in G.items()):continue
                ok=True
                for i in range(v):
                    hi=whole.copy()
                    for t,(a,b) in G.items():
                        if i in (a,b):hi-=lo[a+b-i]-C[t]
                    if hi==lo[i] and (hi in L or hi in C):ok=False
                    if r and sum(len(hi&L[t])>=2 for t in K if t not in S)<2:ok=False
                count+=ok
            if count:found[z]=count
 assert wanted==found,(len(wanted),len(found),set(wanted)^set(found))
 print(ns,len(found),'matching topology classes and point-choice multiplicities',flush=True)
for f in ((0,1,2,3,4,5),(0,1,2,3,4,6)):verify(f)
