"""Exact aggregate rooted selector on a graph with binary linear checksum tags."""
from itertools import combinations, product
from pathlib import Path
import sys
sys.path.append(str(Path(__file__).resolve().parents[1]/"unseeded-root-states"))
from solve import canonical, eliminate, image, solve


def positions(mask):
    while mask:
        bit=mask & -mask
        yield bit.bit_length()-1
        mask^=bit


def basis_indices(cols,order=None):
    piv={}
    chosen=[]
    for i in (range(len(cols)) if order is None else order):
        v=cols[i]
        while v:
            j=v.bit_length()-1
            if j not in piv:
                piv[j]=v
                chosen.append(i)
                break
            v^=piv[j]
    return chosen


class Instance:
    def __init__(self,n,edges,tags,k):
        self.n=n
        self.edges=tuple(edges)
        self.m=len(self.edges)
        self.D=tuple((1<<a)^(1<<b) for a,b in self.edges)
        self.k=k
        self.mask=(1<<k)-1
        tags=tuple(tags)
        self.tags=tuple(a|(b<<k) for a,b in tags)
        if len(tags)!=self.m or any(min(a,b)<0 or max(a,b)>self.mask for a,b in tags):
            raise ValueError("one pair of k-bit gain columns is required per edge")
        self.tree=sum(1<<i for i in basis_indices(self.D))
        self.full=(1<<self.m)-1

    def fundamental(self,tree):
        ids=list(positions(tree))
        cols=tuple(self.D[i] for i in ids)
        if tree.bit_count()!=self.tree.bit_count() or len(canonical(cols))!=len(cols):
            raise ValueError("supplied edge set is not a spanning forest")
        result={}
        for e in positions(self.full^tree):
            path=solve(cols,self.D[e])
            assert path is not None
            result[e]=(1<<e)|sum(1<<ids[i] for i in positions(path))
        return result

    def values(self,signature):
        a,b=signature&self.mask,signature>>self.k
        return (a,b,a^b)

    def chord_targets(self,sigs):
        states={0}
        for sig in sigs:
            states={s^v for s in states for v in self.values(sig)}
        return states

    def on_tree(self,tree,target):
        states={0:(0,0)}
        for cycle in self.fundamental(tree).values():
            new={}
            for s,(f,g) in states.items():
                for color,delta in enumerate(self.values(image(self.tags,cycle)),1):
                    pair=(f^(cycle if color&1 else 0),g^(cycle if color&2 else 0))
                    new.setdefault(s^delta,pair)
            states=new
        return states.get(target)

    def solve_two(self,target):
        if self.k>2:
            raise ValueError("use bounded chord search for more than two checksum bits")
        first=self.on_tree(self.tree,target)
        if first is not None:
            return first
        fundamental=list(self.fundamental(self.tree).values())
        sigs=[image(self.tags,c) for c in fundamental]
        if solve(canonical(x for M in sigs for x in self.values(M)),target) is None:
            return None
        assert target==0 and len([s for s in sigs if s])==1
        h=sum(1<<i for i,s in enumerate(sigs) if s)
        evals=[sum(((c>>e)&1)<<i for i,c in enumerate(fundamental)) for e in range(self.m)]
        allowed=[e for e,v in enumerate(evals) if v!=h]
        coeff=solve(tuple(evals[i] for i in allowed),h)
        if coeff is None:
            return None
        special=[allowed[i] for i in positions(coeff)]
        order=special+[i for i in range(self.m) if i not in special]
        cotree=sum(1<<i for i in basis_indices(evals,order))
        result=self.on_tree(self.full^cotree,target)
        assert result is not None
        return result

    def stabilizer(self,states):
        return {v for v in range(1<<self.k) if {s^v for s in states}==states}

    def finite_certificate(self,tree):
        gains={e:image(self.tags,c) for e,c in self.fundamental(tree).items()}
        keep={}
        states={0}
        for e,gain in gains.items():
            new={s^v for s in states for v in self.values(gain)}
            if len(new)>len(states):
                keep[e]=gain
            else:
                assert new==states
            states=new
        H=self.stabilizer(states)
        assert len(keep)<1<<self.k and states==self.chord_targets(keep.values())
        assert all(set(self.values(M))<=H for e,M in gains.items() if e not in keep)
        return keep,states,H

    def solve_fixed(self,target,tree_with_gains):
        """tree_with_gains(instance, marked-dict) returns a realizing forest or None."""
        direct=self.on_tree(self.tree,target)
        if direct is not None:
            return direct
        initial=self.fundamental(self.tree)
        span=canonical(image(self.tags,cycle) for cycle in initial.values())
        if solve(canonical(v for M in span for v in self.values(M)),target) is None:
            return None
        types=[image(span,i) for i in range(1,1<<len(span))]
        limit=min((1<<self.k)-1,len(initial))
        for size in range(1,limit+1):
            for marked in combinations(range(self.m),size):
                marked_set=set(marked)
                remaining=[e for e in range(self.m) if e not in marked_set]
                reference=sum(1<<j for j in basis_indices(self.D,remaining))
                if reference.bit_count()!=self.tree.bit_count():
                    continue
                residual=[image(self.tags,c) for j,c in self.fundamental(reference).items() if j not in marked_set]
                for gains in product(types,repeat=size):
                    states=self.chord_targets(gains)
                    if target not in states:
                        continue
                    H=self.stabilizer(states)
                    if any(v not in H for M in residual for v in self.values(M)):
                        continue
                    tree=tree_with_gains(self,dict(zip(marked,gains)))
                    if tree is None:
                        continue
                    cycles=self.fundamental(tree)
                    assert all(j in cycles and image(self.tags,cycles[j])==M for j,M in zip(marked,gains))
                    found=self.on_tree(tree,target)
                    assert found is not None
                    return found
        return None

    def physical(self,target,flow):
        """Build canonical X and verify all named dependencies by Gaussian elimination."""
        f,g=flow
        if image(self.D,f) or image(self.D,g):
            raise ValueError("flow fails vertex conservation")
        m,n=self.m,self.n
        tagshift=m+2*n
        columns=[]
        X=0
        for e in range(m):
            color=((f>>e)&1)|(((g>>e)&1)<<1)
            for v,tag in enumerate(self.values(self.tags[e]),1):
                column=(1<<e)|(tag<<tagshift)
                if v&1:
                    column^=self.D[e]<<m
                if v&2:
                    column^=self.D[e]<<(m+n)
                columns.append(column)
                if not color or v==color:
                    X |= 1<<(len(columns)-1)
        roots=(self.full|(target<<tagshift),)+tuple(1<<(tagshift+j) for j in range(self.k))
        chosen=tuple(columns[e] for e in positions(X))
        piv,_=eliminate(chosen)
        residual=[]
        for root in roots:
            v=root
            for i,(row,_) in sorted(piv.items(),reverse=True):
                if v>>i&1:
                    v^=row
            residual.append(v)
        return X,canonical(eliminate(residual)[1])
