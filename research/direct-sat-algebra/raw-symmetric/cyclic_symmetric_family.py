"""Recover diagonal rank-one directions on the raw cyclic d=1 family."""
from itertools import combinations
from quadratic_centroid import independent,zero_combinations
from quadratic_target import apply_basis,evaluate_anf,interpolate,insert,reduce_vector
from raw_symmetric_section import recover


def diagonal_axes(n,r,anf,section):
    """Return diagonal hyperplane basis (packed matrices), and raw leaf axes."""
    raw=lambda x:evaluate_anf(*anf,x)
    def polar(x,y):
        return raw(0)^raw(x)^raw(y)^raw(x^y)
    def pack(cols):
        return sum(v<<(i*r) for i,v in enumerate(cols))
    def action(H,x):
        return apply_basis(tuple((H>>(j*r))&((1<<r)-1) for j in range(r)),x)
    mats=independent(pack([polar(1<<i,l) for l in section.leaves]) for i in range(n))
    d=len(mats)
    if d!=r+1:
        return None
    # Each entry is itself a linear form on crossing-matrix coordinates.
    entries=[[sum(((H>>(i+r*j))&1)<<k for k,H in enumerate(mats)) for j in range(r)] for i in range(r)]
    def multiply(a,b):
        low=a&b
        for k,(i,j) in enumerate(combinations(range(d),2),d):
            low|=((((a>>i)&(b>>j))^((a>>j)&(b>>i)))&1)<<k
        return low
    indices=list(combinations(range(r),2))
    minors=independent(multiply(entries[i][k],entries[j][l])^multiply(entries[i][l],entries[j][k])
                       for i,j in indices for k,l in indices)
    linear=zero_combinations(minors,lambda x:x>>d)
    if len(linear)!=1:
        return None
    diag=tuple(apply_basis(mats,x) for x in zero_combinations(tuple(1<<i for i in range(d)),
                 lambda x:(x&linear[0]).bit_count()%2))
    groups=[tuple(1<<i for i in range(r))]
    for H in diag:
        refined=[]
        for group in groups:
            zeros=tuple(zero_combinations(group,lambda x:action(H,x)))
            if len(zeros) in (0,len(group)):
                refined.append(group)
                continue
            def tests(x):
                val=0
                for D in diag:
                    y=action(D,x)
                    for z in zeros:
                        val=(val<<1)|((z&y).bit_count()%2)
                return val
            complement=tuple(zero_combinations(group,tests))
            if len(independent((*zeros,*complement)))!=len(group) or len(zeros)+len(complement)!=len(group):
                return None
            refined.extend((zeros,complement))
        groups=refined
    if any(len(g)!=1 for g in groups):
        return None
    axes=tuple(g[0] for g in groups)
    if any((x&action(D,y)).bit_count()%2 for x,y in combinations(axes,2) for D in diag):
        return None
    return diag,tuple(apply_basis(section.leaves,x) for x in axes)


def witness(n,r,anf,section,diag,axes,target):
    from hidden_product_network import encoder
    raw=lambda x:evaluate_anf(*anf,x)
    leaf_coordinates=encoder(section.leaves)
    axis_codes=tuple(leaf_coordinates(x) for x in axes)
    def output(y):
        return sum(((y&a).bit_count()%2)<<i for i,a in enumerate(axis_codes))
    def polar(x,y):
        return raw(0)^raw(x)^raw(y)^raw(x^y)
    rows={}
    for i in range(n):
        column=sum(polar(1<<i,l)<<(j*r) for j,l in enumerate(section.leaves))
        insert(column,1<<i,rows)
    lifts=[]
    diagonal_words=[]
    for D in diag:
        rest,x=reduce_vector(D,rows)
        if rest:
            raise ValueError("diagonal matrix outside crossing span")
        lifts.append(x)
        diagonal_words.append(sum(((output(polar(x,y))>>j)&1)<<j for j,y in enumerate(axes)))
    coords=encoder(diagonal_words)
    x=0
    for j in range(r):
        base=raw(x)
        mask=(1<<(j+1))-1
        if len(independent(output(raw(x^y)^base)&mask for y in axes[:j+1]))!=j+1:
            x^=apply_basis(lifts,coords(1<<j))
    base=raw(x)
    cols=[raw(x^y)^base for y in axes]
    x^=apply_basis(axes,encoder(cols)(target^base))
    if raw(x)!=target:
        raise ArithmeticError("target mismatch")
    return x


if __name__=='__main__':
    from random import Random
    from hidden_product_network import encoder
    rng=Random(47)
    def dense(d):
        b=[1<<i for i in range(d)]
        for _ in range(8*d):
            i,j=rng.sample(range(d),2)
            b[i]^=b[j]
        return b
    for r in (7,8,9,11):
        n=2*r+1
        ib,ob=dense(n),dense(r)
        decode=encoder(ib)
        mask=(1<<r)-1
        drift=[rng.randrange(1<<r) for _ in range(n)]
        def raw(x):
            w=decode(x)^117
            c,y=w&mask,(w>>r)&mask
            out=c&y
            for i in range(r):
                j=(i+1)%r
                if w>>(2*r):
                    out^=(((y>>i)&1)<<j)^(((y>>j)&1)<<i)
                out^=(((c>>i)&(c>>((i+2)%r)))&1)<<j
            return apply_basis(ob,out)^apply_basis(drift,x)
        anf=interpolate(raw,n)
        chart=recover(n,r,*anf,max_trials=1)
        assert chart and chart.solution_dimension==1
        diag,axes=diagonal_axes(n,r,anf,chart)
        assert len(diag)==r and set(axes)==set(ib[r:2*r])
        for target in (0,1,mask):
            assert raw(witness(n,r,anf,chart,diag,axes,target))==target
    print('unique pairing, exact hidden axes and raw witnesses at r=7,8,9,11 passed')
