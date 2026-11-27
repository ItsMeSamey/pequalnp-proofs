"""Reduce a known target matching to at most 2b baseline-alternating switches."""


def compress(n, edges, baseline, target_matching, b):
    """Return (reduced edge ids, alternating cycles). Each cycle starts with baseline."""
    if type(n) is not int or type(b) is not int or n<0 or b<0:
        raise ValueError("invalid dimensions")
    edges=[(u,v,tuple(g)) for u,v,g in edges]
    if any(not (0<=u<n and 0<=v<n and u!=v and len(g)==b and all(x in (0,1,2) for x in g))
           for u,v,g in edges):
        raise ValueError("invalid labelled edge")
    def owners(m):
        result={}
        for k in m:
            if not 0<=k<len(edges):
                raise ValueError("invalid matching edge")
            u,v,_=edges[k]
            if u in result or v in result:
                raise ValueError("matching has shared endpoints")
            result[u]=result[v]=k
        if len(result)!=n:
            raise ValueError("matching does not cover all vertices")
        return result
    first=owners(baseline)
    second=owners(target_matching)
    unseen={v for v in first if first[v]!=second[v]}
    cycles=[]
    gains=[]
    while unseen:
        v=start=next(iter(unseen))
        cycle=[]
        gain=[0]*b
        while True:
            for owner,sign in ((first,-1),(second,1)):
                unseen.discard(v)
                edge=owner[v]
                u,w,g=edges[edge]
                cycle.append(edge)
                v=w if u==v else u
                for i,x in enumerate(g):
                    gain[i]=(gain[i]+sign*x)%3
            if v==start:
                break
        if any(gain):
            cycles.append(tuple(cycle))
            gains.append(tuple(gain))
    while len(cycles)>2*b:
        # In the first 2b+1 gains a nonempty zero-sum subsequence always exists.
        paths={(0,)*b:0}
        discard=None
        for i,g in enumerate(gains[:2*b+1]):
            for previous,mask in list(paths.items()):
                new=tuple((a+x)%3 for a,x in zip(previous,g))
                chosen=mask|(1<<i)
                if not any(new):
                    discard=chosen
                    break
                paths.setdefault(new,chosen)
            if discard is not None:
                break
        if discard is None:
            raise AssertionError("zero-sum subsequence missing")
        cycles=[c for i,c in enumerate(cycles) if not (discard>>i)&1]
        gains=[g for i,g in enumerate(gains) if not (discard>>i)&1]
    result=set(first.values())
    for cycle in cycles:
        result.symmetric_difference_update(cycle)
    return tuple(sorted(result)),tuple(cycles)
