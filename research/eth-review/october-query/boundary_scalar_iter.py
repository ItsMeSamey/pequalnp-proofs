"""Count Boolean affine wire constraints and signed OR gates using normal-space boundaries."""
from affine_mst_cnf import add,plug
from signed_cover_projection import sat

def span(rows):
    p={}
    for row in rows: add(row,0,p)
    return tuple(p[j][0] for j in sorted(p,reverse=True))

def intersect(left,right):
    p={}
    out=[]
    for row,tag in [(x,x) for x in left]+[(x,0) for x in right]:
        while row and row.bit_length()-1 in p:
            v,a=p[row.bit_length()-1]
            row^=v
            tag^=a
        if row: p[row.bit_length()-1]=(row,tag)
        elif tag: out.append(tag)
    return span(out)

def expressions(coords,forms):
    p={}
    for i,row in enumerate(coords):
        a=1<<i
        while row and row.bit_length()-1 in p:
            x,v=p[row.bit_length()-1]
            row^=x
            a^=v
        if not row: raise ArithmeticError('dependent basis')
        p[row.bit_length()-1]=(row,a)
    out=[]
    for row in forms:
        a=0
        while row:
            x,v=p[row.bit_length()-1]
            row^=x
            a^=v
        out.append(a)
    return out

def state(w,forms):
    return sum(((w&a).bit_count()%2)<<i for i,a in enumerate(forms))

class Limit(Exception): pass

class Node:
    def __init__(self,index,normals,kids=()):
        self.index,self.normals,self.kids=index,normals,kids

def scalar(n,equations,clauses,*,tree=None,budget,fallback=None):
    """Tree is a binary nesting of physical zero-based clause indices, each once."""
    eqs=tuple(equations)
    cs=tuple(tuple(c) for c in clauses)
    if min(n,budget)<0 or any(not 0<=a<1<<n or b not in (0,1) for a,b in eqs):
        raise ValueError('invalid bounds/equations')
    if any(not 1<=abs(x)<=n for c in cs for x in c): raise ValueError('bad literal')
    p={}
    if not all(add(a,b,p) for a,b in eqs): return dict(status='exact',count=0,witness=None,work=0)
    gates=[tuple(plug(1<<(abs(x)-1),int(x<0),p) for x in c) for c in cs]
    if tree is None:
        layer=list(range(len(cs)))
        while len(layer)>1:
            layer=[(layer[i],layer[i+1]) if i+1<len(layer) else layer[i]
                   for i in range(0,len(layer),2)]
        tree=layer[0] if layer else None
    seen=set()
    stack=[(tree,False)]
    built=[]
    while stack:
        t,finish=stack.pop()
        if finish:
            r=built.pop()
            l=built.pop()
            built.append(Node(None,span(l.normals+r.normals),(l,r)))
        elif t is None and not cs:
            built.append(Node(None,()))
        elif isinstance(t,int):
            if not 0<=t<len(cs) or t in seen: raise ValueError('invalid leaf')
            seen.add(t)
            built.append(Node(t,span(a for a,b in gates[t])))
        elif isinstance(t,(tuple,list)) and len(t)==2:
            stack.extend(((None,True),(t[1],False),(t[0],False)))
        else: raise ValueError('invalid tree')
    root=built.pop()
    if len(seen)!=len(cs): raise ValueError('incomplete tree')
    work=peak=0
    dims=[]
    def pay(d,c):
        nonlocal work,peak
        cost=(1<<d)*max(1,c)
        if cost>budget-work: raise Limit
        work+=cost
        peak=max(peak,d)
        dims.append(d)
    def compute(node):
        border=node.border
        tab={}
        if node.kids:
            l,r=node.kids
            bl,br=l.border,r.border
            joint=span(bl+br)
            pay(len(joint),len(bl)+len(br)+len(border)+4)
            L,R,B=(expressions(joint,x) for x in (bl,br,border))
            for w in range(1<<len(joint)):
                a,b=state(w,L),state(w,R)
                if a not in l.entries or b not in r.entries: continue
                key=state(w,B)
                val=l.entries[a][0]*r.entries[b][0]
                old,rep=tab.get(key,(0,(a,b)))
                tab[key]=old+val,rep
        else:
            gate=gates[node.index] if node.index is not None else ()
            pay(len(node.normals),len(gate)+len(border)+2)
            B=expressions(node.normals,border)
            E=expressions(node.normals,[a for a,b in gate])
            for w in range(1<<len(node.normals)):
                if node.index is not None and not any(((a&w).bit_count()%2)^b for a,(_,b) in zip(E,gate)): continue
                key=state(w,B)
                old,rep=tab.get(key,(0,w))
                tab[key]=old+1,rep
        node.entries=tab
        return border
    try:
        stack=[(root,(),False)]
        while stack:
            node,exterior,finish=stack.pop()
            if finish:
                compute(node)
                continue
            node.border=intersect(node.normals,exterior)
            if node.kids:
                l,r=node.kids
                # Child exterior intersections depend only on its sibling and
                # the current boundary, not on an explicit global outside basis.
                stack.extend(((node,(),True),(r,span(node.border+l.normals),False),
                              (l,span(node.border+r.normals),False)))
            else: compute(node)
    except Limit:
        if fallback is None: return dict(status='budget',work=work,max_dimension=peak)
        count,w=fallback(n,eqs,cs)
        status='fallback'
    else:
        status='exact'
        if 0 not in root.entries: count,w=0,None
        else:
            count=root.entries[0][0]<<(n-len(p)-len(root.normals))
            stack=[(root,0)]
            while stack:
                node,key=stack.pop()
                ans=node.entries[key][1]
                if node.kids:
                    stack.extend(zip(node.kids,ans))
                else:
                    for j,a in enumerate(node.normals):
                        if not add(a,ans>>j&1,p): raise ArithmeticError('trace mismatch')
            w=0
            for j,(a,b) in sorted(p.items()):
                if ((w&a).bit_count()%2)^b: w|=1<<j
    if not isinstance(count,int) or not 0<=count<=1<<n or (count==0)!=(w is None): raise ValueError('bad count')
    if w is not None and (not 0<=w<1<<n or any((w&a).bit_count()%2!=b for a,b in eqs) or
                          not all(sat(c,w) for c in cs)): raise ValueError('bad witness')
    return dict(status=status,count=count,witness=w,work=work,max_dimension=peak,state_dimensions=tuple(dims))

def network(net,*,budget,tree=None,fallback=None):
    """Read actual raw wire IDs at each factor port; retain both network and source counts."""
    port={end:i for i,wire in enumerate(net.wires) for end in wire}
    eqs=[]
    clauses=[]
    for v,(kind,data) in enumerate(net.atoms):
        ids=[port[v,i] for i in range(len(net.scopes[v]))]
        if kind=='affine':
            for h,b in data:
                a=0
                for i,z in enumerate(ids):
                    if h>>i&1: a^=1<<z
                eqs.append((a,b))
        elif kind=='copy':
            eqs.extend(((1<<ids[0])^(1<<j),0) for j in ids[1:])
        elif kind=='clause':
            clauses.append(tuple((-1 if data>>i&1 else 1)*(z+1) for i,z in enumerate(ids)))
        elif kind!='free': raise ValueError('unsupported local tensor')
    result=scalar(len(net.wires),eqs,clauses,tree=tree,budget=budget,fallback=fallback)
    if result['status']=='budget': return result
    obs=0
    w=result['witness']
    if w is not None:
        for (v,i),j in port.items():
            if w>>j&1: obs|=1<<net.scopes[v][i]
        raw=net.lift(obs)
        if raw is None: raise ArithmeticError('original witness failed')
    else: raw=None
    return dict(result,network_count=result['count'],wire_witness=w,
                count=result['count']*net.fiber,witness=raw)
