"""Recognize the strict signed padded-pair CNF class and count it by planar dimers.

Public count(n, clauses) returns None outside the recognized class. NetworkX
(planar embedding via check_planarity) is required for recognized instances.
Literal IDs are signed and one-based. Repeated physical clauses are rejected.
"""
from collections import Counter,defaultdict,deque
from fractions import Fraction
from itertools import combinations
from math import comb,isqrt,lcm,prod


def _faces(graph,nx):
    planar,embedding=nx.check_planarity(graph)
    if not planar:
        return None
    dart_face={}
    boundaries=[]
    for u in embedding:
        for v in embedding.neighbors_cw_order(u):
            if (u,v) in dart_face:
                continue
            boundary=embedding.traverse_face(u,v)
            darts=list(zip(boundary,boundary[1:]+boundary[:1]))
            for dart in darts:
                dart_face[dart]=len(boundaries)
            boundaries.append(darts)
    return dart_face,boundaries


def _determinant(matrix):
    """Fraction-free determinant with row pivoting."""
    a=[row[:] for row in matrix]
    n=len(a)
    if not n:
        return 1
    sign=previous=1
    for k in range(n-1):
        pivot=next((i for i in range(k,n) if a[i][k]),None)
        if pivot is None:
            return 0
        if pivot!=k:
            a[k],a[pivot]=a[pivot],a[k]
            sign=-sign
        value=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                q,rem=divmod(a[i][j]*value-a[i][k]*a[k][j],previous)
                if rem:
                    raise ArithmeticError("nonexact Bareiss division")
                a[i][j]=q
        previous=value
    return sign*a[-1][-1]


def _matching_sum(graph,nx):
    if len(graph)%2:
        return Fraction(0)
    faces=_faces(graph,nx)
    if faces is None:
        raise ArithmeticError("decorated graph is not planar")
    dart_face,boundaries=faces
    opposite=defaultdict(list)
    orientation={}
    for u,v in graph.edges:
        key=min(u,v),max(u,v)
        orientation[key]=key
        a,b=dart_face[u,v],dart_face[v,u]
        if a!=b:
            opposite[a].append((b,key))
            opposite[b].append((a,key))
    # Choose face 0 as outer face; traverse_face keeps the same side at each dart.
    parent={0:None}
    bfs=[0]
    for f in bfs:
        for other,key in opposite[f]:
            if other not in parent:
                parent[other]=(f,key)
                bfs.append(other)
    if len(parent)!=len(boundaries):
        raise ArithmeticError("dual spanning tree disconnected")
    for f in reversed(bfs[1:]):
        aligned=sum(orientation[min(u,v),max(u,v)]==(u,v) for u,v in boundaries[f])
        if aligned%2==0:
            _,key=parent[f]
            u,v=orientation[key]
            orientation[key]=v,u
    scale=1
    for _,_,data in graph.edges(data=True):
        scale=lcm(scale,data['weight'].denominator)
    n=len(graph)
    A=[[0]*n for _ in range(n)]
    for key,(u,v) in orientation.items():
        w=graph[u][v]['weight']*scale
        if w.denominator!=1:
            raise ArithmeticError("weight scaling failed")
        A[u][v],A[v][u]=w.numerator,-w.numerator
    det=_determinant(A)
    root=isqrt(det)
    if root*root!=det:
        raise ArithmeticError("skew determinant is not square")
    return Fraction(root,scale**(n//2))


def _decorated(base,ratios,nx):
    faces=_faces(base,nx)
    if faces is None:
        return None
    _,boundaries=faces
    H=nx.Graph()
    dart_port={}
    def edge(u,v,w=Fraction(1)):
        if u==v or H.has_edge(u,v):
            raise ArithmeticError("unexpected parallel matching port")
        H.add_edge(u,v,weight=w)
    for darts in boundaries:
        prior=None
        for j,dart in enumerate(darts):
            # Each trivalent-path site has one original port and up to two chain ports.
            first=len(H)
            arity=1+int(j>0)+int(j+1<len(darts))
            ports=list(range(first,first+arity))
            H.add_nodes_from(ports)
            for u,v in combinations(ports,2):
                edge(u,v)
            dart_port[dart]=first
            if prior is not None:
                edge(prior,ports[1])
            prior=ports[-1] if j+1<len(darts) else None
    for u,v in base.edges:
        edge(dart_port[u,v],dart_port[v,u],ratios[min(u,v),max(u,v)])
    return H


def count(n,clauses):
    if not isinstance(n,int) or n<0:
        raise ValueError("invalid number of variables")
    raw=Counter()
    positive=Counter()
    used=set()
    for row in clauses:
        row=tuple(row)
        if any(not isinstance(l,int) or not 1<=abs(l)<=n for l in row):
            raise ValueError("invalid literal")
        if len(row)!=3 or len({abs(l) for l in row})!=3:
            return None
        raw[tuple(sorted(row))]+=1
        positive.update(l for l in row if l>0)
        used.update(abs(l) for l in row)
    if not raw or any(v!=1 for v in raw.values()):
        return None
    basevars={v for v in used if positive[v]>=2}
    selectors={v for v in used if positive[v]==1}
    padding=used-basevars-selectors
    pairs=defaultdict(dict)
    neg_neighbors=defaultdict(set)
    for row in raw:
        if all(l<0 for l in row):
            vs={-l for l in row}
            for z in vs&selectors:
                neg_neighbors[z].update(vs-{z})
            continue
        zs=[l for l in row if l in selectors]
        ends=[l for l in row if abs(l) in basevars]
        if len(zs)!=1 or len(ends)!=2 or (ends[0]>0)!=(ends[1]>0):
            return None
        key=tuple(sorted(map(abs,ends)))
        sign=ends[0]>0
        if sign in pairs[key]:
            return None
        pairs[key][sign]=zs[0]
    if not pairs or any(len(zs)!=2 for zs in pairs.values()):
        return None
    expected=Counter()
    seen=set()
    allz=set()
    ratios={}
    prefactor=2
    for (u,v),zs in pairs.items():
        sizes=[]
        for sign,z in zs.items():
            block=neg_neighbors[z]
            if z in allz or len(block)<2 or not block<=padding or seen&block:
                return None
            allz.add(z)
            seen.update(block)
            sizes.append(len(block))
            expected[tuple(sorted((u if sign else -u,v if sign else -v,z)))]+=1
            for triple in combinations(sorted(block|{z}),3):
                expected[tuple(sorted(-l for l in triple))]+=1
        if sizes[0]!=sizes[1]:
            return None
        b=sizes[0]
        forced=1+b
        free=forced+1+b+comb(b,2)
        ratios[u,v]=Fraction(forced,free)
        prefactor*=free**2
    if expected!=raw or allz!=selectors or seen!=padding:
        return None
    import networkx as nx
    base=nx.Graph()
    base.add_nodes_from(basevars)
    base.add_edges_from(pairs)
    if min(dict(base.degree()).values())<2 or not nx.is_connected(base):
        return None
    H=_decorated(base,ratios,nx)
    if H is None:
        return None
    scaled=prefactor*_matching_sum(H,nx)
    if scaled.denominator!=1:
        raise ArithmeticError("nonintegral original count")
    return scaled.numerator<<(n-len(used))
