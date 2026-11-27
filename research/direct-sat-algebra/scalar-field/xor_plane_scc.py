"""Polynomial sufficient certificate for absence via a supplied XOR filter."""
from four_minor_pair_filters import planes, accepts, common_basis
from punctured_chart import coordinates
from quadratic_centroid import independent


def projected(form, columns):
    a,b=planes[form]
    return [((x>>4)<<2)|((a&x).bit_count()&1)|(((b&x).bit_count()&1)<<1) for x in columns]


def shifted_kernel(left,right,basis):
    lcoords=coordinates(tuple(left[j] for j in basis))
    rcoords=coordinates(tuple(right[j] for j in basis))
    v=[rcoords(x) for x in right]
    return [sum(((a&lcoords(x)).bit_count()&1)<<i for i,a in enumerate(v)) for x in left]


def reach(matrix,vertex):
    reached=1<<vertex
    while True:
        grown=reached
        for j,neighbors in enumerate(matrix):
            if reached>>j&1:
                grown |= neighbors
        if reached==grown:
            return reached
        reached=grown


def certify_absence(columns,first,second):
    """True certifies no target H=<e0,e1>; False is inconclusive."""
    columns=tuple(columns)
    if accepts(first,1)==accepts(second,1):
        return False
    rank=len(independent(x>>4 for x in columns))+2
    left,right=(projected(f,columns) for f in first)
    other_left,other_right=(projected(f,columns) for f in second)
    anchor=common_basis(left,right,rank)
    if anchor is None:
        return common_basis(other_left,other_right,rank) is None
    if any(len(independent(M[j] for j in anchor))!=rank for M in (other_left,other_right)):
        return False
    a=shifted_kernel(left,right,anchor)
    b=shifted_kernel(other_left,other_right,anchor)
    union=[x|y for x,y in zip(a,b)]
    reaches=[reach(union,j) for j in range(len(columns))]
    blocks={tuple(j for j in range(len(columns)) if (reaches[i]>>j)&(reaches[j]>>i)&1)
            for i in range(len(columns))}
    for block in blocks:
        same=all((a[j]>>i&1)==(b[j]>>i&1) for i in block for j in block)
        transposed=all((a[j]>>i&1)==(b[i]>>j&1) for i in block for j in block)
        if not same and not transposed:
            return False
    return True


if __name__=='__main__':
    from check_xor_plane_filter import columns
    from itertools import combinations
    from random import Random
    from four_minor_pair_filters import trace
    assert certify_absence(columns,(1,40),(31,45))
    rng=Random(1552)
    tested=0
    for _ in range(120):
        r=rng.randrange(4)
        cols=rng.sample(range(1,1<<(4+r)),r+5)
        target=any(trace(cols,idx)==1 for idx in combinations(range(len(cols)),r+2))
        if len(independent(x>>4 for x in cols))!=r:
            continue
        f,g,h,k=rng.choices(sorted(planes),k=4)
        if certify_absence(cols,(f,g),(h,k)):
            assert not target
        tested+=1
    print(tested,'random soundness controls and fixed strict-separation certificate passed')
