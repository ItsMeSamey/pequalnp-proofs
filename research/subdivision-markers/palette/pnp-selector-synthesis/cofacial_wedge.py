"""Exact wedge generators using a verified marked outer-face rotation and first-space backend."""
from functools import lru_cache
from itertools import combinations,product
from five_terminal_dual import neutral_generators
from planar_moment_certificate import CertifiedDual


def marked_order(dual,rotation,access):
    """access[v] is the incoming neighbor of the chosen visit to v in the outer face walk."""
    n=len(dual.graph)
    if len(rotation)!=n or set(access)!=set(dual.terminals):
        raise ValueError("rotation/terminal access mismatch")
    for u,ring in enumerate(rotation):
        expected={v for v,_ in dual.graph[u] if v!=u}
        if len(ring)!=len(expected) or set(ring)!=expected:
            raise ValueError("rotation must list the simple shadow neighbors once")
    darts={(u,v) for u,ring in enumerate(rotation) for v in ring}
    edge_count=len(darts)//2
    corners={(pred,v) for v,pred in access.items()}
    if not corners<=darts:
        raise ValueError("invalid terminal access corner")
    order=[];faces=0
    while darts:
        start=next(iter(darts));u,v=start
        marked=[]
        while True:
            darts.remove((u,v))
            if (u,v) in corners:
                marked.append(v)
            ring=rotation[v];u,v=v,ring[ring.index(u)-1]
            if (u,v)==start:
                break
        faces+=1
        if marked:
            if order:
                raise ValueError("marked terminal corners span different faces")
            order=marked[::-1]
    if n-edge_count+(faces or 1)!=2:
        raise ValueError("rotation is not spherical")
    return tuple(order)


@lru_cache(maxsize=None)
def _patterns(n):
    if not n:
        return ((),)
    answers=[]
    for bits in range(1<<(n-1)):
        block=(0,)+tuple(j for j in range(1,n) if bits>>(j-1)&1)
        intervals=list(zip(block,block[1:]+(n,)))
        for subs in product(*(_patterns(b-a-1) for a,b in intervals)):
            part=[block]
            for sub,(a,b) in zip(subs,intervals):
                part.extend(tuple(x+a+1 for x in item) for item in sub)
            answers.append(tuple(part))
    return tuple(answers)


def ear_path(u,v,allowed,rotation,access):
    """Return a canonical outer boundary path as a vertex set, or None."""
    here=v;previous=access[v];seen=set()
    walk=[v];position={v:0}
    while here!=u:
        state=(previous,here)
        if state in seen:
            return None
        seen.add(state)
        ring=rotation[here];i=ring.index(previous)
        nxt=next((ring[(i-j)%len(ring)] for j in range(1,len(ring)+1)
                  if ring[(i-j)%len(ring)] in allowed),None)
        if nxt is None:
            return None
        if nxt in position:
            for w in walk[position[nxt]+1:]:
                del position[w]
            del walk[position[nxt]+1:]
        else:
            position[nxt]=len(walk);walk.append(nxt)
        previous,here=here,nxt
    return set(walk)


def anchors(part,order,rotation,access):
    remaining=set(range(len(rotation)));live=list(order);blocks=list(map(set,part));result=[]
    while blocks:
        for j,block in enumerate(blocks):
            if block==set(live):
                sequence=live;break
            starts=[i for i,v in enumerate(live) if v in block and live[i-1] not in block]
            if len(starts)==1:
                i=starts[0];sequence=(live[i:]+live[:i])[:len(block)];break
        else:
            return None
        group={sequence[0]}
        allowed=remaining-(set(live)-block)
        for u,v in zip(sequence,sequence[1:]):
            p=ear_path(u,v,allowed,rotation,access)
            if p is None:
                return None
            group.update(p)
        result.append(sum(1<<w for w in group))
        remaining-=group;live=[v for v in live if v not in block];blocks.pop(j)
    return result


def generators(n,edges,rotation,access,first_space):
    """rotation is counterclockwise; private outputs retain the supplied edge indexing."""
    dual=CertifiedDual(n,edges);rotation=tuple(tuple(r) for r in rotation);access=dict(access)
    order=marked_order(dual,rotation,access)
    if not order:
        return ((dual.cut(1<<u),dual.cut(1<<v)) for u,v in combinations(range(n-1),2))
    def stream():
        yield from neutral_generators(dual,first_space)
        for pattern in _patterns(len(order)):
            if len(pattern)<3:
                continue
            part=[tuple(order[j] for j in block) for block in pattern]
            for block in part:
                charge=0
                for v in block:charge^=dual.charge[v]
                if charge:
                    break
            else:
                system=anchors(part,order,rotation,access)
                if system is not None:
                    for x,y in combinations(system,2):
                        if not dual.compatible(x,y):
                            raise ValueError("invalid reconstructed anchor pair")
                        yield dual.cut(x),dual.cut(y)
    return stream()
