"""Deterministic exact ternary-labelled planar matching count and edge witness."""
from itertools import product
from math import isqrt
import networkx as nx


def _orient(graph):
    directed=set()
    for cc in nx.connected_components(graph):
        sub=graph.subgraph(cc)
        planar,emb=nx.check_planarity(sub)
        if not planar:
            raise ValueError("graph is not planar")
        face={}
        faces=[]
        seen=set()
        for u,v in emb.edges:
            if (u,v) in seen:
                continue
            boundary=emb.traverse_face(u,v,seen)
            arcs=list(zip(boundary,boundary[1:]+boundary[:1]))
            for e in arcs:
                face[e]=len(faces)
            faces.append(arcs)
        if not faces:
            continue
        dual=[[] for _ in faces]
        for u,v in sub.edges:
            directed.add((min(u,v),max(u,v)))
            i,j=face[u,v],face[v,u]
            if i!=j:
                dual[i].append((j,(u,v)))
                dual[j].append((i,(u,v)))
        parent={0:None}
        order=[0]
        for i in order:
            for j,e in dual[i]:
                if j not in parent:
                    parent[j]=e
                    order.append(j)
        for i in reversed(order[1:]):
            if sum(e in directed for e in faces[i])%2==0:
                u,v=parent[i]
                if (u,v) not in directed:
                    u,v=v,u
                directed.remove((u,v))
                directed.add((v,u))
    return directed


def _det(a):
    if not a:
        return 1
    denom=sign=1
    for k in range(len(a)-1):
        row=next((i for i in range(k,len(a)) if a[i][k]),None)
        if row is None:
            return 0
        if row!=k:
            a[k],a[row]=a[row],a[k]
            sign=-sign
        pivot=a[k][k]
        for i in range(k+1,len(a)):
            for j in range(k+1,len(a)):
                a[i][j]=(pivot*a[i][j]-a[i][k]*a[k][j])//denom
        denom=pivot
    return sign*a[-1][-1]


def count(n,edges,target):
    """Return (original edge-set count, one tuple of original edge IDs or None)."""
    edges=[(u,v,tuple(g)) for u,v,g in edges]
    target=tuple(target)
    if type(n) is not int or n<0 or any(type(x) is not int or x not in (0,1,2) for x in target):
        raise ValueError("invalid problem dimensions")
    graph=nx.Graph()
    graph.add_nodes_from(range(n))
    for u,v,g in edges:
        if (any(type(i) is not int or not 0<=i<n for i in (u,v)) or u==v or len(g)!=len(target)
            or any(type(x) is not int or x not in (0,1,2) for x in g)):
            raise ValueError("invalid edge")
        graph.add_edge(u,v)
    orientation=_orient(graph)
    width=len(edges)+1
    mask=(1<<width)-1
    def mass(vertices,goal):
        if len(vertices)%2:
            return 0
        pos={v:i for i,v in enumerate(sorted(vertices))}
        es=[(pos[u],pos[v],g,1 if (u,v) in orientation else -1)
            for u,v,g in edges if u in pos and v in pos]
        def partition(chi):
            a=[[0]*len(pos) for _ in pos]
            for i,j,g,s in es:
                residue=sum(x*y for x,y in zip(chi,g))%3
                a[i][j]+=s*(1<<(width*residue))
                a[j][i]=-a[i][j]
            det=_det(a)
            val=isqrt(det)
            assert val*val==det
            return val
        total=partition(())
        if not total:
            return 0
        acc=total
        for chi in product(range(3),repeat=len(goal)):
            if next((x for x in chi if x),0)!=1:
                continue
            want=sum(x*y for x,y in zip(chi,goal))%3
            digits=partition(chi)>>(width*want)
            selected=0
            while digits:
                selected+=digits&mask
                digits>>=3*width
            acc+=3*selected-total
        value,rem=divmod(acc,3**len(goal))
        assert not rem and 0<=value<=total
        return value
    verts=set(range(n))
    result=mass(verts,target)
    if not result:
        return 0,None
    kept=[]
    residual=target
    while verts:
        u=min(verts)
        for k,(a,b,g) in enumerate(edges):
            if u not in (a,b) or a not in verts or b not in verts:
                continue
            reduced=verts-{a,b}
            goal=tuple((x-y)%3 for x,y in zip(residual,g))
            if mass(reduced,goal):
                kept.append(k)
                verts,residual=reduced,goal
                break
        else:
            raise AssertionError("positive mass without a partner")
    assert sorted(v for k in kept for v in edges[k][:2])==list(range(n))
    assert all(sum(edges[k][2][j] for k in kept)%3==t for j,t in enumerate(target))
    return result,tuple(kept)
