"""Linear reduction for one or two prescribed path components; rows/columns use bit masks."""
from itertools import combinations

def reduce_vec(x,piv):
    mask=0
    for j in sorted(piv,reverse=True):
        if x>>j&1:
            h,k=piv[j]
            x^=h;mask^=k
    return x,mask

def basis(cols):
    piv={}
    for i,col in enumerate(cols):
        x,used=reduce_vec(col,piv)
        if not x:return None
        piv[x.bit_length()-1]=(x,used^(1<<i))
    return piv

def is_circuit(cols):
    if not cols:return False
    x=0
    for c in cols:x^=c
    return not x and basis(cols[:-1]) is not None

def exhaustive_oracle(cols,ports):
    """Finite reference implementation; use the represented binary triple algorithm at scale."""
    free=sorted(set(range(len(cols)))-set(ports))
    for w in range(len(free)+1):
        for subset in combinations(free,w):
            idx=list(ports)+list(subset)
            if is_circuit([cols[i] for i in idx]):return idx
    return None

def reduce_paths(n,edges,D,paths,oracle=exhaustive_oracle):
    """Each disjoint prescribed path is listed in order as (edge_id,from,to) triples."""
    if not paths or len(paths)>2:raise ValueError('one or two path components expected')
    roots={i for path in paths for i,_,_ in path}
    strict={b for path in paths for _,_,b in path[:-1]}
    reps=[path[0][0] for path in paths]
    X=sorted(roots-set(reps))
    ids=[i for i,(a,b,g) in enumerate(edges) if i in roots or (a not in strict and b not in strict)]
    def augmented(i):
        a,b,g=edges[i]
        return (1<<a)^(1<<b)^(D*g)^((g^(i==reps[0]))<<n)
    piv=basis([augmented(j) for j in X])
    if piv is None:return None
    remain=[j for j in ids if j not in X]+[None]
    cols=[augmented(j) if j is not None else 1<<n for j in remain]
    quot=[reduce_vec(x,piv)[0] for x in cols]
    ports=[remain.index(j) for j in reps]+[len(remain)-1]
    circ=oracle(quot,ports)
    if circ is None:return None
    x=0
    for i in circ:x^=cols[i]
    residual,mask=reduce_vec(x,piv)
    assert not residual
    found={remain[i] for i in circ if remain[i] is not None}
    found.update(j for k,j in enumerate(X) if mask>>k&1)
    assert roots<=found
    assert is_circuit([(1<<edges[i][0])^(1<<edges[i][1])^(D*edges[i][2]) for i in found])
    assert not sum(edges[i][2] for i in found)%2
    return found
