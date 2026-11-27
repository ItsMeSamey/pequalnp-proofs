"""Recover one indexed seven-terminal grove from a nonzero exact evaluation."""
def recover(n,edges,weights,groups,field,evaluate):
    edges=tuple(tuple(e) for e in edges);values=list(weights);groups=tuple(map(frozenset,groups))
    if len(edges)!=len(values) or field.q<n-2:raise ValueError("weights or field size")
    if not evaluate(values):return None
    forced=[];coeff={}
    for e,w in enumerate(values):
        values[e]=0
        k=len(forced)
        if k not in coeff:
            denominators=[]
            for x in range(k+1):
                den=1
                for y in range(k+1):
                    if x!=y:den=field.mul(den,x^y)
                denominators.append(field.inv(den))
            coeff[k]=denominators
        result=0
        for x,d in enumerate(coeff[k]):
            marked=values.copy()
            for f in forced:marked[f]=field.mul(x,values[f])
            result^=field.mul(d,evaluate(marked))
        if not result:
            values[e]=w
            forced.append(e)
    parts=[{i} for i in range(n)]
    for e in forced:
        u,v=edges[e]
        a=next(s for s in parts if u in s);b=next(s for s in parts if v in s)
        if a is b:raise ValueError("oracle returned a cycle")
        parts.remove(b);a.update(b)
    marks=set.union(*(set(g) for g in groups))
    if len(parts)!=3 or {frozenset(c&marks) for c in parts}!=set(groups) or any(not values[e] for e in forced):
        raise ValueError("oracle failed original indexed witness verification")
    return tuple(forced)
