"""Finite scheduled L=2 packet recursion, with frozen mixed-degree vertex descriptors."""
from dataclasses import dataclass
from itertools import product
from collections import Counter
from one_packet_layer import Ring, canonical_lift, polynomial_at_shift, interpolate, recover
from packet_entry_tape import packet_entry


@dataclass(frozen=True)
class Table:
    birth:int
    values:tuple
    def word(self,bits):
        return self.values[sum(b<<j for j,b in enumerate(bits))]


@dataclass(frozen=True)
class Packet:
    ring:Ring
    rows:tuple
    columns:tuple
    kernel:tuple
    target:tuple
    source:tuple
    equal:bool
    @property
    def birth(self):
        return self.ring.p
    def word(self,bits):
        r=self.ring
        zero,one=r.scalar(0),r.scalar(1)
        Y=bits[:len(self.rows)]
        X=dict(zip(self.columns,bits[len(Y):]))
        affine=[]
        for idx,(slot,y) in enumerate(zip(self.rows,Y)):
            base=zero
            for j,x in X.items():
                if x:
                    base=r.add(base,self.kernel[j-slot+1])
            terms=[] if self.equal else [(idx,self.kernel[1] if y else r.neg(self.kernel[1]))]
            affine.append((base if y else r.add(one,r.neg(base)),terms))
        return packet_entry(r,affine,self.target,[(r.scalar(X[j]),e) for j,e in self.source])


def evaluate(network,m,p,field,ell,depth,schedule,stats=None):
    """Sides list (descriptor, ordered edge IDs). Scheduled packets encode two edge
    IDs (or None), an equal-symbol flag and first row label. Old vertices stay intact."""
    if stats is None:
        stats=Counter()
    r=Ring(p,field,ell)
    stats['calls']+=1
    for side in network:
        if sorted(e for desc,edges in side for e in edges)!=list(range(m)):
            raise ValueError('each edge must occur once per side')
    if not depth or not m:
        stats['leaf_assignments']+=1<<m
        total=r.scalar(0)
        for x in range(1<<m):
            term=r.scalar(1)
            for side in network:
                for desc,edges in side:
                    value=desc.word(tuple((x>>j)&1 for j in edges))
                    stats['entry_reads']+=1
                    stats['packet_reads']+=isinstance(desc,Packet)
                    term=r.mul(term,canonical_lift(value,desc.birth,p))
            total=r.add(total,term)
        return total
    packets=schedule(network,m,depth)
    layout=[{},{}]
    for k,(e0,e1,equal,first) in enumerate(packets):
        for s,e in enumerate((e0,e1)):
            if e is None:
                continue
            for side in range(2):
                if e in layout[side]:
                    raise ValueError('duplicate slot')
                layout[side][e]=(k,s,first if equal else first^s^side)
    for side in range(2):
        if set(layout[side])!=set(range(m)):
            raise ValueError('incomplete layout')
        for desc,edges in network[side]:
            if not edges or len({layout[side][e][2] for e in edges})!=1:
                raise ValueError('positive-degree vertices must remain in one group')
    degree=3*m
    if degree+1>1<<len(field):
        raise ValueError('field too small for interpolation')
    pt=p+16*degree+16*m
    rr=Ring(pt,field,ell)
    points=[tuple((j>>b)&1 for b in range(len(field)))+(0,)*(len(field)*(ell-1)) for j in range(degree+1)]
    jets={}
    for t in (-1,1):
        vals=[]
        for zeta in points:
            kernel=tuple(polynomial_at_shift(rr,t,zeta,d) for d in (-1,0,1))
            modes=[(k,s) for k,(e0,e1,equal,_) in enumerate(packets) if not equal
                   for s,e in enumerate((e0,e1)) if e is not None]
            total=rr.scalar(0)
            for exps in product((0,1),repeat=len(modes)):
                if sum(exps)>=pt:
                    continue
                beta=dict(zip(modes,exps))
                term=rr.scalar(1)
                for g in (0,1):
                    names={}
                    retained=[]
                    born=[]
                    for side in range(2):
                        for desc,edges in network[side]:
                            if layout[side][edges[0]][2]!=g:
                                continue
                            ids=[]
                            for e in edges:
                                names[side,e]=len(names)
                                ids.append(names[side,e])
                            retained.append((desc,tuple(ids)))
                    for k,(_,_,equal,_) in enumerate(packets):
                        lists=[sorted((s,names[side,e]) for e,(q,s,label) in layout[side].items()
                                      if q==k and label==g) for side in range(2)]
                        rows,cols=[tuple(s for s,_ in lst) for lst in lists]
                        if not rows and not cols:
                            continue
                        desc=Packet(rr,rows,cols,kernel,() if equal else tuple(beta[k,s] for s in rows),
                                    () if equal else tuple((s,beta[k,s]) for s in cols),equal)
                        born.append((desc,tuple(v for lst in lists for _,v in lst)))
                        stats['packet_births']+=1
                    term=rr.mul(term,evaluate((retained,born),len(names),pt,field,ell,depth-1,schedule,stats))
                total=rr.add(total,term)
                stats['tuple_products']+=1
            vals.append(total)
        jets[t]=interpolate(rr,points,vals)[:degree]
    return tuple(recover(1,1,m,p,len(field)*ell,lambda t,j,c,prec:jets[t][j][c]))
