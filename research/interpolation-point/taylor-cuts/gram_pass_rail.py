"""Exact trace counting for a supplied oriented-pass order, without tensor expansion."""
from fractions import Fraction
from math import prod
from commuting_toggle_rails import compose


def _compress(weights,limit):
    tensors=list(weights)
    if not tensors:
        return {},0
    def inner(a,b):
        return prod(sum(x==y for x,y in zip(p,q)) for p,q in zip(a,b))
    gram=[[inner(a,b) for b in tensors] for a in tensors]
    rows=[[Fraction(v) for v in row]+[sum(v*weights[b] for v,b in zip(row,tensors))]
          for row in gram]
    pivots=[]
    for j in range(len(tensors)):
        i=len(pivots)
        q=next((q for q in range(i,len(rows)) if rows[q][j]),None)
        if q is None:
            continue
        if limit is not None and i>=limit:
            raise ValueError("reachable rank exceeds budget")
        rows[q],rows[i]=rows[i],rows[q]
        d=rows[i][j]
        rows[i]=[v/d for v in rows[i]]
        for t in range(len(rows)):
            if t!=i and rows[t][j]:
                d=rows[t][j]
                rows[t]=[a-d*b for a,b in zip(rows[t],rows[i])]
        pivots.append(j)
    # Keep zero-weight basis members: the reported rank is the reachable span.
    return {tensors[j]:rows[i][-1] for i,j in enumerate(pivots)},len(pivots)


def prepare_passes(n,size,passes,order):
    order=tuple(order)
    if n<0 or size<1 or sorted(order)!=list(range(1,n+1)):
        raise ValueError("invalid dimension or common control order")
    position={v:i for i,v in enumerate(order)}
    ident=tuple(range(size))
    directions=[]; by_pass=[]
    for forward,gates in passes:
        if forward not in (True,False):
            raise ValueError("invalid pass orientation")
        local={}; previous=-1
        for lit,p,q in gates:
            if abs(lit) not in position or sorted(p)!=list(ident) or sorted(q)!=list(ident):
                raise ValueError("invalid signed gate")
            j=position[abs(lit)] if forward else n-1-position[abs(lit)]
            if j<previous:
                raise ValueError("invalid common-order pass")
            previous=j
            opts=(tuple(q),tuple(p)) if lit<0 else (tuple(p),tuple(q))
            prior=local.get(abs(lit),(ident,ident))
            local[abs(lit)]=tuple(compose(opts[v],prior[v]) for v in (0,1))
        directions.append(forward);by_pass.append(local)
    return order,ident,directions,by_pass


def count_passes(n,size,passes,order,*,rank_limit=None,with_witness=True):
    """passes = (forward_bool, signed gates) pairs in rail order; controls are 1-based.

    A gate is (literal, P0, P1), as in commuting_toggle_rails. Return the joint
    closed-state/control count, a (control-mask,start) witness or None, and peak rank.
    """
    order,ident,directions,by_pass=prepare_passes(n,size,passes,order)
    def run(fixed):
        basis={(ident,)*len(by_pass):Fraction(1)};rank=1
        if rank_limit is not None and rank>rank_limit:
            raise ValueError("reachable rank exceeds budget")
        for v in order:
            new={}
            for tensor,w in basis.items():
                for b in ((fixed[v],) if v in fixed else (0,1)):
                    state=[]
                    for p,forward,local in zip(tensor,directions,by_pass):
                        a=local.get(v,(ident,ident))[b]
                        state.append(compose(a,p) if forward else compose(p,a))
                    t=tuple(state);new[t]=new.get(t,0)+w
            basis,current=_compress(new,rank_limit)
            rank=max(rank,current)
        count=Fraction(0)
        for t,w in basis.items():
            perm=ident
            for p in t:
                perm=compose(p,perm)
            count+=w*sum(x==y for x,y in enumerate(perm))
        assert count.denominator==1 and count>=0
        return int(count),rank
    count,rank=run({})
    if not count or not with_witness:
        return count,None,rank
    fixed={}
    for v in order:
        fixed[v]=0
        if not run(fixed)[0]:
            fixed[v]=1
    perm=ident
    for forward,local in zip(directions,by_pass):
        for v in (order if forward else reversed(order)):
            perm=compose(local.get(v,(ident,ident))[fixed[v]],perm)
    start=next(i for i,j in enumerate(perm) if i==j)
    mask=sum(b<<(v-1) for v,b in fixed.items())
    return count,(mask,start),rank
