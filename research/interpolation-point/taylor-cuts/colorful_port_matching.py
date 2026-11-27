"""One coloring of base matching pairs, in the order supplied in base_ids."""
from collections import deque


def search_coloring(n,edges,base_ids,target,colors):
    """Return original edge IDs or None if no colorful switch family reaches target."""
    edges=[(a,b,tuple(g)) for a,b,g in edges]
    base_ids=tuple(base_ids)
    colors=tuple(colors)
    target=tuple(target)
    if (n<0 or len(colors)!=len(base_ids) or any(type(c) is not int or c<0 for c in colors)
            or any(t not in (0,1,2) for t in target)
            or any(not(0<=a<n and 0<=b<n and a!=b and len(g)==len(target)
                       and all(x in (0,1,2) for x in g)) for a,b,g in edges)
            or any(not 0<=i<len(edges) for i in base_ids)
            or sorted(v for i in base_ids for v in edges[i][:2])!=list(range(n))):
        raise ValueError("invalid matching, coloring, labels or graph")
    def plus(x,y):
        return tuple((a+b)%3 for a,b in zip(x,y))
    palette={c:j for j,c in enumerate(sorted(set(colors)))}
    bits=[1<<palette[c] for c in colors]
    zero=(0,)*len(target)
    goal=tuple((v-sum(edges[i][2][j] for i in base_ids))%3 for j,v in enumerate(target))
    if goal==zero:
        return base_ids
    # State is the entry vertex; mate[state] is its exit.
    pair={}
    mate={}
    for j,i in enumerate(base_ids):
        a,b,_=edges[i]
        pair[a]=pair[b]=j
        mate[a],mate[b]=b,a
    arcs=[[] for _ in range(n)]
    cycles={}
    for i,(a,b,g) in enumerate(edges):
        for u,v in ((a,b),(b,a)):
            j=pair[u]
            gain=tuple((x-y)%3 for x,y in zip(g,edges[base_ids[j]][2]))
            if j==pair[v]:
                if i!=base_ids[j]:
                    cycles.setdefault((bits[j],gain),(i,))
            else:
                arcs[mate[u]].append((v,gain,i))
    for start in range(n):
        first=(bits[pair[start]],start,zero)
        parents={first:None}
        queue=deque([first])
        while queue:
            key=queue.popleft()
            mask,u,gain=key
            for v,delta,i in arcs[u]:
                total=plus(gain,delta)
                if v==start:
                    slot=(mask,total)
                    if slot not in cycles:
                        path=[i]
                        step=key
                        while parents[step] is not None:
                            step,e=parents[step]
                            path.append(e)
                        cycles[slot]=tuple(reversed(path))
                elif not mask&bits[pair[v]]:
                    nxt=(mask|bits[pair[v]],v,total)
                    if nxt not in parents:
                        parents[nxt]=key,i
                        queue.append(nxt)
    # Each transition consumes new colors, so predecessor pointers are acyclic.
    parents={(0,zero):None}
    queue=deque(parents)
    while queue:
        key=queue.popleft()
        mask,gain=key
        for (cm,delta),path in cycles.items():
            if mask&cm:
                continue
            nxt=mask|cm,plus(gain,delta)
            if nxt in parents:
                continue
            parents[nxt]=key,path
            if nxt[1]!=goal:
                queue.append(nxt)
                continue
            chosen=set(base_ids)
            while parents[nxt] is not None:
                nxt,path=parents[nxt]
                for i in path:
                    for v in edges[i][:2]:
                        chosen.discard(base_ids[pair[v]])
                chosen.update(path)
            result=tuple(sorted(chosen))
            if (sorted(v for i in result for v in edges[i][:2])!=list(range(n)) or
                any(sum(edges[i][2][j] for i in result)%3!=t for j,t in enumerate(target))):
                raise ArithmeticError("original matching failed replay")
            return result
    return None
