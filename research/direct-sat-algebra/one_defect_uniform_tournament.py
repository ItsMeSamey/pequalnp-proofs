"""Quadratic-time odd-mark / uniform odd-indegree tournament witness."""
from collections import deque


def components(vertices,edge):
    """Tournament SCCs in forward order, via sorted indegrees and tight prefixes."""
    order=sorted(vertices,key=lambda v:sum(edge(u,v) for u in vertices if u!=v))
    parts=[]
    start=0
    cross=0
    for j,v in enumerate(order,1):
        cross+=sum(edge(u,v) for u in vertices if u!=v)-(j-1)
        if cross==0:
            parts.append(order[start:j])
            start=j
    return parts


def search(rows,beta,*,offset=None):
    """Rows are (Gz)_v; off-diagonal bit u in row v denotes u -> v.
    Optional packed affine offset toggles the raw diagonal in the selected-row test.
    """
    n=len(rows)
    if offset is None:
        offset=0
    if any(not 0<=r<1<<n for r in (*rows,beta,offset)):
        raise ValueError("invalid matrix, mark, or affine offset")
    # Unpack once, keeping the quadratic bound for the graph operations.
    bits=[[(b>>j)&1 for b in r.to_bytes((n+7)//8,'little') for j in range(8)][:n] for r in rows]
    def edge(u,v):
        return bits[v][u]
    if any((bits[i][i]^(offset>>i&1))!=1 for i in range(n)):
        raise ValueError("requires uniform odd effective indegrees")
    if any(edge(i,j)==edge(j,i) for i in range(n) for j in range(i)):
        raise ValueError("expected tournament")
    A=[i for i in range(n) if beta>>i&1]
    if not A:
        return None
    def cross_witness(a,p,q):
        for u in p:
            for v in q:
                if edge(v,u):
                    return (a,u,v)
        raise AssertionError("failed cut should contain a backwards arc")
    def triangle(C):
        a=C[0]
        return cross_witness(a,[u for u in C[1:] if edge(u,a)],[v for v in C[1:] if edge(a,v)])
    marked=components(A,edge)
    for C in marked:
        if len(C)>1:
            return triangle(C)
    A=[C[0] for C in marked]
    unmarked=components([i for i in range(n) if not beta>>i&1],edge)
    B=[u for C in unmarked for u in C]
    boundaries={0}
    pos=0
    for C in unmarked:
        pos+=len(C)
        boundaries.add(pos)
    cuts=[]
    for a in A:
        p=[u for u in B if edge(u,a)]
        k=len(p)
        if k not in boundaries or B[:k]!=p:
            return cross_witness(a,p,[u for u in B if edge(a,u)])
        cuts.append(k)
    front=next((i for i,C in enumerate(unmarked) if len(C)>1),len(unmarked))
    if front<len(unmarked):
        for a,k in zip(A,cuts):
            if k>front:
                return (*triangle(unmarked[front]),a)
    # All retained cuts lie before the first cyclic component.
    highright=[len(A)-1]*len(A)
    for j in reversed(range(len(A)-1)):
        r=highright[j+1]
        highright[j]=j if cuts[j]>=cuts[r] else r
    left=0
    for j in range(1,len(A)-1):
        r=highright[j+1]
        if min(cuts[left],cuts[r])>cuts[j]:
            return (A[left],A[j],A[r],B[cuts[j]])
        if cuts[j]>cuts[left]:
            left=j
    return None
