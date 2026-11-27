"""Sum mode histories by group splits; no histogram in the production DFS."""
from dataclasses import dataclass


@dataclass
class Work:
    adds: int = 0
    muls: int = 0
    leaf_calls: int = 0
    live: int = 0
    peak: int = 0

    def hold(self, n):
        self.live += n
        self.peak = max(self.peak, self.live)


def choices(ids, modes, beta, budget):
    """Stream crossing tuples of weighted cost at most budget."""
    ids = tuple(ids)
    if not ids:
        yield 0
        return
    for j in ids:
        beta[j] = 0
    spent = 0
    while True:
        yield spent
        for j in reversed(ids):
            weight, cap = modes[j][2:]
            if beta[j] < cap and spent + weight <= budget:
                beta[j] += 1
                spent += weight
                break
            spent -= beta[j]*weight
            beta[j] = 0
        else:
            return


def evaluate(groups, modes, precision, leaf, ring, method='scalar', tag=None):
    """Modes = (source,target,positive weight,finite cap), leaf reads its incidents.
    Ring = (zero,one,add,mul); tag optionally supplies audit weight markers.
    Stored-return count tracks array/scalar slots, excluding operation temporaries.
    """
    zero,one,add,mul=ring
    work=Work()
    beta=[0]*len(modes)
    budget=precision-1
    assert all(u in groups and v in groups and u!=v and w>0 and k>=0
               for u,v,w,k in modes)
    def plus(x,y):
        work.adds+=1
        return add(x,y)
    def times(x,y):
        work.muls+=1
        return mul(x,y)
    def call(g):
        work.leaf_calls+=1
        return leaf(g,beta)
    if method=='literal':
        out=[zero]*precision
        work.hold(precision+1)
        for w in choices(list(range(len(modes))),modes,beta,budget):
            val=one
            for g in groups:
                val=times(val,call(g))
            out[w]=plus(out[w],val)
        return out,work
    assert method in ('scalar','histogram')
    def visit(gs,left):
        n=1 if method=='scalar' else left+1
        work.hold(n)
        if len(gs)==1:
            z=call(gs[0])
            return z if method=='scalar' else [z]+[zero]*left
        A,B=gs[:len(gs)//2],gs[len(gs)//2:]
        cut=[j for j,(u,v,_,_) in enumerate(modes)
             if (u in A and v in B) or (v in A and u in B)]
        out=zero if method=='scalar' else [zero]*n
        for w in choices(cut,modes,beta,left):
            a=visit(A,left-w)
            b=visit(B,left-w)
            if method=='scalar':
                z=times(a,b)
                if tag is not None:
                    z=times(z,tag(w))
                out=plus(out,z)
            else:
                for i,ai in enumerate(a):
                    for j in range(left-w-i+1):
                        out[w+i+j]=plus(out[w+i+j],times(ai,b[j]))
            work.hold(-2*(1 if method=='scalar' else left-w+1))
            del a,b
        return out
    return visit(tuple(groups),budget),work
