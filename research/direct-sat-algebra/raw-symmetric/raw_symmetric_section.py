"""Discover and verify symmetric binary-pencil sections from packed raw ANF."""
from dataclasses import dataclass
from hidden_product_network import encoder
from quadratic_centroid import independent
from quadratic_target import affine_domain,apply_basis,evaluate_anf,interpolate


@dataclass
class Section:
    leaves: tuple
    centers: tuple
    raw: object
    solution_dimension: int

    def witness(self,target):
        r=len(self.leaves)
        if not 0<=target<1<<r:
            raise ValueError("target outside output")
        for word in range(1<<r):
            x=apply_basis(self.centers,word)
            base=self.raw(x)
            cols=tuple(self.raw(x^y)^base for y in self.leaves)
            if len(independent(cols))!=r:
                continue
            result=x^apply_basis(self.leaves,encoder(cols)(target^base))
            if self.raw(result)!=target:
                raise ArithmeticError("raw witness mismatch")
            return result
        raise ArithmeticError("certified parity failed")


def recover(n,r,constant,linear,pairs,*,max_trials=None):
    """Try every basis element first. None means no certificate was found."""
    if n<2*r or r<1:
        return None
    if len(linear)!=n or any(not 0<=v<1<<r for v in (constant,*linear,*pairs.values())):
        raise ValueError("invalid packed ANF")
    if any(not 0<=i<j<n for i,j in pairs):
        raise ValueError("invalid quadratic monomial")
    rows=[[0]*n for _ in range(n)]
    for (i,j),v in pairs.items():
        rows[i][j]=rows[j][i]=v
    equations=[]
    for row in rows:
        contractions=[sum(((v>>i)&1)<<j for j,v in enumerate(row)) for i in range(r)]
        for i in range(r):
            for j in range(i):
                equations.append(((contractions[i]<<(n*j))^(contractions[j]<<(n*i)),0))
    _,space,_=affine_domain(n*r,equations)
    raw=lambda x:evaluate_anf(constant,linear,pairs,x)
    def candidates():
        yield from space
        for bits in range(1,1<<len(space)):
            if bits.bit_count()>1:
                yield apply_basis(space,bits)
    for trial,phi in enumerate(candidates()):
        if max_trials is not None and trial>=max_trials:
            break
        leaves=tuple((phi>>(n*i))&((1<<n)-1) for i in range(r))
        columns=[tuple(apply_basis(row,y) for y in leaves) for row in rows]
        masks=tuple(sum(((col[i]>>i)&1)<<k for k,col in enumerate(columns)) for i in range(r))
        if len(independent(masks))!=r:
            continue
        if any(apply_basis(tuple(col[i] for col in columns),v)
               for i in range(r) for v in leaves[:i]):
            continue
        centers=tuple(affine_domain(n,[(a,int(k==j)) for k,a in enumerate(masks)])[0] for j in range(r))
        return Section(leaves,centers,raw,len(space))
    return None


def solve(n,r,constant,linear,pairs,target,*,max_trials=None):
    chart=recover(n,r,constant,linear,pairs,max_trials=max_trials)
    return ('UNKNOWN',None) if chart is None else ('SAT',chart.witness(target))


if __name__=='__main__':
    from random import Random
    rng=Random(684)
    def basis(d):
        b=[1<<k for k in range(d)]
        for _ in range(10*d):
            i,j=rng.sample(range(d),2)
            b[i]^=b[j]
        return b
    dimensions=[]
    for r in (3,4,5):
        n=2*r+1
        ib,ob=basis(n),basis(r)
        mask=(1<<r)-1
        coeff={(i,j):rng.randrange(1<<r) for i in range(r) for j in range(i)}
        drift=[rng.randrange(1<<r) for _ in range(n)]
        center_square={(i,j):rng.randrange(1<<r) for i in range(r) for j in range(i)}
        def raw(x):
            z=apply_basis(ib,x)^7
            t,y=z&mask,(z>>r)&mask
            v=(t&y)^apply_basis(drift,z)^1
            for (i,j),a in coeff.items():
                if (a&t).bit_count()&1:
                    v^=(((y>>j)&1)<<i)^(((y>>i)&1)<<j)
                if (t>>i)&(t>>j)&1:
                    v^=center_square[i,j]
            if z>>(2*r):
                v^=t
            return apply_basis(ob,v)
        anf=interpolate(raw,n)
        chart=recover(n,r,*anf)
        assert chart
        dimensions.append(chart.solution_dimension)
        for target in range(1<<r):
            assert raw(chart.witness(target))==target
    assert 1 in dimensions
    assert recover(6,3,0,[0]*6,{},max_trials=24) is None
    assert solve(3,2,0,[0]*3,{(0,1):1,(1,2):2},0)==('UNKNOWN',None)
    print('56 witnesses; symmetry-space dimensions',dimensions)
