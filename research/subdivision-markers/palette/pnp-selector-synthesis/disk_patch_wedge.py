"""Paired-space tracebacks from a checked disk patch with boundary identifications."""
from itertools import combinations
from cofacial_wedge import anchors,_patterns
from planar_moment_certificate import CertifiedDual
from five_terminal_dual import neutral_generators


def _check_patch(dual,rotation,order,access,image):
    n=len(rotation);marks=set(order)
    if not order or len(marks)!=len(order) or set(access)!=marks or len(image)!=n or not marks<=set(range(n)):
        raise ValueError("invalid marked patch")
    if set(image)!=set(range(len(dual.graph))) or not set(dual.terminals)<={image[v] for v in marks}:
        raise ValueError("missing original vertices or charges")
    for u in set(range(n))-marks:
        if image.count(image[u])!=1:
            raise ValueError("identified unmarked vertex")
    shadow=set()
    for u,ring in enumerate(rotation):
        if len(ring)!=len(set(ring)) or u in ring:
            raise ValueError("invalid simple rotation")
        for v in ring:
            if not 0<=v<n or u not in rotation[v]:
                raise ValueError("asymmetric adjacency")
            if image[u]!=image[v]:
                shadow.add(tuple(sorted((image[u],image[v]))))
    if shadow!={tuple(sorted((a,b))) for a,b,_ in dual.edges if a!=b}:
        raise ValueError("quotient shadow mismatch")
    # Add a test frame outside access corners, never used for actual routing.
    size=max(3,len(order))
    frame=[list(r) for r in rotation]+[[] for _ in range(size)]
    for i in range(size):
        u=n+i;prev=n+(i-1)%size;nxt=n+(i+1)%size
        if i<len(order):
            v=order[i];source=access[v]
            if frame[v]:
                if source not in frame[v]:
                    raise ValueError("bad marked corner")
                frame[v].insert(frame[v].index(source),u)
            else:
                if source is not None:
                    raise ValueError("isolated mark has no incoming edge")
                frame[v].append(u)
            frame[u]=[nxt,v,prev]
        else:
            frame[u]=[nxt,prev]
    seen={0};todo=[0]
    for u in todo:
        for v in frame[u]:
            if v not in seen:
                seen.add(v);todo.append(v)
    if len(seen)!=len(frame):
        raise ValueError("unframed patch component")
    darts={(u,v) for u,r in enumerate(frame) for v in r}
    edges=len(darts)//2;faces=0
    while darts:
        start=next(iter(darts));u,v=start
        while True:
            darts.remove((u,v))
            ring=frame[v];u,v=v,ring[ring.index(u)-1]
            if (u,v)==start:break
        faces+=1
    if len(frame)-edges+faces!=2:
        raise ValueError("patch disks/corners do not give a sphere frame")


def generators(n,edges,rotation,order,access,image,first_space):
    dual=CertifiedDual(n,edges)
    if not dual.terminals:
        return ((dual.cut(1<<a),dual.cut(1<<b)) for a,b in combinations(range(n-1),2))
    rotation=tuple(tuple(r) for r in rotation)
    order=tuple(order);access=dict(access);image=tuple(image)
    _check_patch(dual,rotation,order,access,image)
    def stream():
        yield from neutral_generators(dual,first_space)
        for pattern in _patterns(len(order)):
            blocks=[tuple(order[i] for i in part) for part in pattern]
            if len(blocks)<3 or any(len(part)>1 and any(not rotation[v] for v in part) for part in blocks):
                continue
            masklist=anchors(blocks,order,rotation,access)
            if masklist is None:
                continue
            groups=[]
            for mask in masklist:
                new=0
                while mask:
                    bit=mask&-mask;new|=1<<image[bit.bit_length()-1];mask^=bit
                keep=[]
                for old in groups:
                    if old&new:new|=old
                    else:keep.append(old)
                groups=keep+[new]
            if len(groups)<3:
                continue
            good=True
            for mask in groups:
                q=0
                for v in dual.terminals:
                    if mask>>v&1:q^=dual.charge[v]
                if q:
                    good=False;break
            if good:
                for a,b in combinations(groups,2):
                    if not dual.compatible(a,b):
                        raise ValueError("invalid quotient anchor")
                    yield dual.cut(a),dual.cut(b)
    return stream()
