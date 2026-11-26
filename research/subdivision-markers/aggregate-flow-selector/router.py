"""Construct gain-constrained spanning forests with a disjoint-paths solver."""
from itertools import combinations, product
from selector import basis_indices, canonical, image, positions, solve


def route_forest(instance, marked, linkage):
    """linkage(n, edges=[(u,v,gain)], demands=[(s,t,gain)]) returns edge-ID paths."""
    edges, gains = instance.edges, instance.tags
    tasks = []
    for e, sig in marked.items():
        a, b = edges[e]
        need = sig ^ gains[e]
        if a == b:
            if need:
                return None
        else:
            tasks.append((a,b,need))
    remaining = [e for e in range(len(edges)) if e not in marked]
    def complete(forced):
        forced = list(forced)
        if len(basis_indices(instance.D, forced)) < len(forced):
            return None
        tree = sum(1<<e for e in basis_indices(instance.D,forced + remaining))
        return tree if tree.bit_count()==instance.tree.bit_count() else None
    base = complete([])
    if base is None or not tasks:
        return base
    ends = sorted({v for a,b,_ in tasks for v in (a,b)})
    other = sorted(set(range(instance.n)) - set(ends))
    for count in range(min(len(other),len(ends)-2)+1):
        for more in combinations(other,count):
            sites = ends + list(more)
            candidate = list(combinations(sites,2))
            for nseg in range(1,len(sites)):
                for shape in combinations(candidate,nseg):
                    cols = tuple((1<<a)^(1<<b) for a,b in shape)
                    if len(canonical(cols))!=nseg:
                        continue
                    deg = {a:sum(a in e for e in shape) for a in sites}
                    if min(deg.values())==0 or any(deg[a]<3 for a in more):
                        continue
                    paths = [solve(cols,(1<<a)^(1<<b)) for a,b,_ in tasks]
                    if any(p is None for p in paths):
                        continue
                    # Each demanded path must use the matching sum of segment labels.
                    # Unused segments can be omitted in the shape enumeration.
                    if any(all((p>>j)&1==0 for p in paths) for j in range(nseg)):
                        continue
                    clones = {a:[] for a in sites}
                    np = instance.n
                    pairs = []
                    for a,b in shape:
                        clones[a].append(np)
                        clones[b].append(np+1)
                        pairs.append((np,np+1))
                        np += 2
                    graph, original = [], []
                    for e in remaining:
                        a,b = edges[e]
                        if a==b:
                            continue
                        for v,label in ((a,gains[e]),(b,0)):
                            for u in clones.get(v,[v]):
                                graph.append((u,np,label))
                                original.append(e)
                        np += 1
                    for sigs in product(range(1<<(2*instance.k)),repeat=nseg):
                        if any(image(sigs,p)!=t[2] for p,t in zip(paths,tasks)):
                            continue
                        routed=linkage(np,graph,[(a,b,s) for (a,b),s in zip(pairs,sigs)])
                        if routed is None:
                            continue
                        union={original[j] for p in routed for j in p}
                        tree=complete(union)
                        assert tree is not None
                        fc=instance.fundamental(tree)
                        assert all(image(gains,fc[e])==s for e,s in marked.items())
                        return tree
    return None


def brute_linkage(n,edges,demands):
    """Exhaustive oracle for tiny checks. The theorem uses Liu and Yoo instead."""
    adjacency=[[] for _ in range(n)]
    for i,(a,b,s) in enumerate(edges):
        adjacency[a].append((b,s,i))
        adjacency[b].append((a,s,i))
    terminals={v for a,b,_ in demands for v in (a,b)}
    def visit(j,used):
        if j==len(demands):
            return []
        start,end,want=demands[j]
        def walk(v,score,path,seen):
            if v==end:
                if score==want:
                    rest=visit(j+1,used|seen)
                    if rest is not None:
                        return [path]+rest
                return None
            for u,s,e in adjacency[v]:
                if u in used or u in seen or u in terminals and u!=end:
                    continue
                result=walk(u,score^s,path+[e],seen|{u})
                if result is not None:
                    return result
            return None
        return walk(start,0,[],{start})
    return visit(0,set())
