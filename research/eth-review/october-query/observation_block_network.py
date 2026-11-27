"""Verified block covers of a raw signed-CNF affine image, with Boolean wire descriptors."""
from dataclasses import dataclass
from affine_mst_cnf import add,plug
from signed_cover_projection import normalized,sat

@dataclass(frozen=True)
class Result:
    n:int
    raw:tuple
    ids:tuple
    eqs:tuple
    rank:int
    fiber:int
    atoms:tuple
    wires:tuple
    scopes:tuple

    def entry(self,node,w):
        kind,data=self.atoms[node]
        arity=len(self.scopes[node])
        if not 0<=w<1<<arity: raise ValueError('invalid port word')
        if kind=='affine': return int(all((h&w).bit_count()%2==b for h,b in data))
        if kind=='clause': return int(bool((w^data)&((1<<arity)-1)))
        if kind=='copy': return int(w in (0,(1<<arity)-1))
        return 1

    def observed(self,w):
        if not 0<=w<1<<len(self.ids): raise ValueError('invalid observation')
        return all(self.entry(i,sum((w>>j&1)<<k for k,j in enumerate(s)))
                   for i,s in enumerate(self.scopes))

    def lift(self,w):
        if not self.fiber or not self.observed(w): return None
        p={}
        for a,b in self.eqs: add(a,b,p)
        for i,x in enumerate(self.ids):
            if not add(1<<(x-1),w>>i&1,p): raise ArithmeticError('unreachable')
        z=0
        for i,(a,b) in sorted(p.items()):
            if ((a&z).bit_count()%2)^b: z|=1<<i
        if not all(sat(c,z) for c in self.raw): raise ArithmeticError('witness mismatch')
        return z

def compile(n,clauses,ids,blocks,*,incidence_cap):
    """ids = ordered distinct raw variables; blocks use zero-based positions in ids.
    None denotes a failed cover, unrepresented residual, or wire construction cap.
    Wire descriptors are pairs of (node, local port index); graph is bipartite.
    """
    raw=tuple(tuple(c) for c in clauses)
    ids=tuple(ids)
    if n<0 or incidence_cap<0 or len(set(ids))!=len(ids) or any(not 1<=x<=n for x in ids):
        raise ValueError('invalid inputs')
    if any(not 1<=abs(x)<=n for c in raw for x in c): raise ValueError('invalid literal')
    rows=normalized(raw)
    groups={}
    for c in rows:
        if c: groups.setdefault((sum(1<<(abs(x)-1) for x in c),sum(x<0 for x in c)%2),[]).append(c)
    piv={}
    eqs=[]
    def contradiction(): return Result(n,raw,ids,(),0,0,(('clause',0),),(),((),))
    for (a,b),g in groups.items():
        if len(g)==1<<(a.bit_count()-1):
            if not add(a,b^1,piv): return contradiction()
            eqs.append((a,b^1))
            rows.difference_update(g)
    directions=[plug(1<<(x-1),0,piv) for x in ids]
    first={a:(i,b) for i,(a,b) in enumerate(directions)}
    indices={x:i for i,x in enumerate(ids)}
    independent={}
    for a,_ in directions: add(a,0,independent)
    rank=len(independent)
    atoms=[]
    scopes=[]
    inc=0
    def node(kind,data,s):
        atoms.append((kind,data))
        scopes.append(tuple(s))
        return len(atoms)-1
    for c in rows:
        terms=[(x,*plug(1<<(abs(x)-1),int(x<0),piv)) for x in sorted(c)]
        false={}
        if not all(add(a,b,false) for _,a,b in terms): continue
        ports=[]
        neg=0
        for x,a,b in terms:
            if not a: continue
            if a not in first: return None
            j=indices.get(abs(x),first[a][0])
            neg|=(b^directions[j][1])<<len(ports)
            ports.append(j)
        if not ports: return contradiction()
        inc+=len(ports)
        if inc>incidence_cap: return None
        node('clause',neg,ports)
    dual={}
    for block in blocks:
        s=tuple(block)
        if len(set(s))!=len(s) or any(not 0<=j<len(ids) for j in s): raise ValueError('invalid block')
        inc+=len(s)
        if inc>incidence_cap: return None
        p={}
        checks=[]
        for i,j in enumerate(s):
            a,b=directions[j]
            mask=1<<i
            while a and a.bit_length()-1 in p:
                t,u,v=p[a.bit_length()-1]
                a^=t
                mask^=u
                b^=v
            if a: p[a.bit_length()-1]=(a,mask,b)
            else:
                checks.append((mask,b))
                h=sum(1<<s[t] for t in range(len(s)) if mask>>t&1)
                add(h,0,dual)
        if checks: node('affine',tuple(checks),s)
    if len(dual)!=len(ids)-rank: return None
    ends=[[] for _ in ids]
    for i,s in enumerate(scopes):
        for t,j in enumerate(s): ends[j].append((i,t))
    wires=[]
    def wire(a,b,j):
        mid=node('copy',None,(j,j))
        wires.extend(((a,(mid,0)),(b,(mid,1))))
    for j,ports in enumerate(ends):
        while len(ports)<2: ports.append((node('free',None,(j,)),0))
        while len(ports)>2:
            v=node('copy',None,(j,j,j))
            wire(ports.pop(),(v,0),j)
            wire(ports.pop(),(v,1),j)
            ports.append((v,2))
        wire(ports[0],ports[1],j)
    return Result(n,raw,ids,tuple(eqs),rank,1<<(n-len(piv)-rank),tuple(atoms),tuple(wires),tuple(scopes))
