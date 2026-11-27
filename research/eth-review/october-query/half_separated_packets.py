"""Full padded Appendix-D template with opposite-half placement of every COPY2 resource."""
from collections import Counter,defaultdict
from itertools import combinations_with_replacement,product
from packet_layout import construct as source_labels

def build(network,m,*,r,a,u,delta,slot_cap,labels=None,strict=True):
    if min(a,u,delta)<1 or not 1<=u<=a or r<2 or m<1 or slot_cap<0:
        raise ValueError('invalid parameters')
    L=1<<a
    R=r**a
    D=R*R
    if strict and (m<2*D*D*delta or m<L*D or 2*L>delta):
        return dict(status='unknown',reason='source admission')
    if D*L>slot_cap: return dict(status='unknown',reason='minimum padded size')
    sides=tuple(tuple((desc,tuple(ps)) for desc,ps in side) for side in network)
    if len(sides)!=2 or any(sorted(e for _,ps in side for e in ps)!=list(range(m)) for side in sides):
        raise ValueError('bad wire enumeration')
    if any(len(ps)>delta for side in sides for _,ps in side) or any(len(ps)!=2 for _,ps in sides[1]):
        raise ValueError('wrong degree or missing COPY2 pair')
    if labels is None:
        _,_,_,full=source_labels(sides,m,r,a,a,delta,strict=False)
        labels=tuple(tuple(tuple(full[i][s][v] for i in range(a)) for v in range(len(sides[s]))) for s in (0,1))
    else: labels=tuple(tuple(tuple(label) for label in side) for side in labels)
    if len(labels)!=2 or any(len(labels[s])!=len(sides[s]) for s in (0,1)) or any(
        len(label)!=a or any(not 0<=x<r for x in label) for side in labels for label in side):
        raise ValueError('invalid vertex labels')
    owner=[[None]*m for _ in (0,1)]
    for s,side in enumerate(sides):
        for v,(_,ps) in enumerate(side):
            for e in ps: owner[s][e]=labels[s][v]
    cls=list(zip(*owner))
    load=Counter(cls)
    H=((max(load.values())+L-1)//L)*L
    total=H*D
    varnum=D*sum(x*x for x in load.values())-m*m
    if strict and (varnum>2*m*delta*D or total>3*m):
        return dict(status='unknown',reason='label variance or padding')
    if total>slot_cap: return dict(status='unknown',reason='padded slot cap',required=total)
    # Orient the class multigraph by Euler walks after adding a dummy hub at odd vertices.
    adj=defaultdict(list)
    byedge={}
    for j,(_,ps) in enumerate(sides[1]):
        a0,b0=ps
        x,y=cls[a0],cls[b0]
        adj[x].append((j,y))
        adj[y].append((j,x))
        byedge[j]=(a0,b0)
    extra=len(byedge)
    for x in tuple(adj):
        if len(adj[x])%2:
            adj[x].append((extra,None))
            adj[None].append((extra,x))
            extra+=1
    used=set()
    supply=defaultdict(list)
    for start in tuple(adj):
        stack=[start]
        while stack:
            x=stack[-1]
            while adj[x] and adj[x][-1][0] in used: adj[x].pop()
            if not adj[x]:
                stack.pop()
                continue
            j,y=adj[x].pop()
            used.add(j)
            stack.append(y)
            if j in byedge:
                i,k=byedge[j]
                if cls[i]!=x: i,k=k,i
                supply[x,0].append(i)
                supply[y,1].append(k)
    if any(len(s)>H//2 for s in supply.values()): raise ArithmeticError('Euler balance failed')
    packets=[]
    metadata=[]
    pairs=tuple(combinations_with_replacement(range(r),2))
    for pattern in product(pairs,repeat=a):
        mask=sum(1<<i for i,(x,y) in enumerate(pattern) if x!=y)
        for flip in range(L):
            if flip&~mask: continue
            for _ in range(H//L):
                slots=[]
                for j in range(L):
                    orient=(j^flip)&mask
                    x=tuple(pair[orient>>i&1] for i,pair in enumerate(pattern))
                    y=tuple(pair[1-(orient>>i&1)] for i,pair in enumerate(pattern))
                    bucket=supply.get(((x,y),int(j>=L//2)))
                    slots.append(bucket.pop() if bucket else None)
                packets.append(tuple(slots))
                metadata.append((pattern,flip))
    if any(supply.values()) or len(packets)*L!=total: raise ArithmeticError('padding construction failed')
    halves={e:int(j>=L//2) for pk in packets for j,e in enumerate(pk) if e is not None}
    if len(halves)!=m or any(halves[x]==halves[y] for _,(x,y) in sides[1]): raise ArithmeticError('split failed')
    shells=tuple(tuple(tuple(v[i] for v in side) for side in labels) for i in range(u))
    return dict(status='exact',plan=(a,u,tuple(packets),shells),metadata=tuple(metadata),
                labels=labels,H_pad=H,padded_slots=total,variance_numerator=varnum,
                strict=strict)

def from_clauses(n,clauses,**parameters):
    """Use the exact original signed-CNF root wiring; labels are attached to original vertices."""
    from source_grid_cnf_band import _compile
    gates,unused,constant,_=_compile(n,clauses)
    if constant is not None: return dict(status='constant',raw_count=constant)
    m=sum(len(ps) for _,ps,_ in gates)
    network=(tuple(((kind,w),ps) for kind,ps,w in gates),
             tuple(('copy2',(e,e+1)) for e in range(0,m,2)))
    return dict(build(network,m,**parameters),gates=gates,unused_raw_bits=unused)
