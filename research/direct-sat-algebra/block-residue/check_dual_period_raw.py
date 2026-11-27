"""04-only oracle for dual consequences, original flags and theta potentials."""
from itertools import product
from random import Random
from biclique_dual import biclique_dual_witness, dual_directions


def span(vectors):
    values={0}
    for v in vectors:
        values |= {x^v for x in values}
    return values


def certify(pairs):
    spaces=[span(v for pair,b in zip(pairs,bits) for v in pair[b])
            for bits in product((0,1),repeat=len(pairs))]
    exact=set.intersection(*spaces)
    directions=dual_directions(pairs)
    certified=span(directions)
    assert len(certified)==1<<len(directions)
    assert certified <= exact
    return certified,exact


def flag_checks(cols,groups,rank):
    def syndrome(w):
        result=0
        for col,b in zip(cols,w):
            if b:result^=col
        return result
    def legal(w):
        return all(not(any(w[i] for i in A) and any(w[i] for i in B)) for A,B in groups)
    possible={syndrome(w) for w in product((0,1),repeat=len(cols)) if legal(w)}
    for target in range(1<<rank):
        ans=biclique_dual_witness(cols,target,groups)
        assert (ans is not None)==(target in possible)
        if ans is not None:assert len(ans)==len(cols) and legal(ans) and syndrome(ans)==target


def theta():
    cols=[1]*4+[2]*4+[3]*4
    groups=[((0,1),(4,5)),((6,7),(8,9)),((10,11),(2,3))]
    shores=[([cols[i] for i in A],[cols[i] for i in B]) for A,B in groups]
    assert all(span(a)&span(b)=={0} and span(a)!=span(b) for a,b in shores)
    assert certify(shores)==(set(range(4)),set(range(4)))
    paths=[(0,2+3*j,3+3*j,4+3*j,1) for j in range(3)]
    endpoints=[(u,v) for path in paths for u,v in zip(path,path[1:])]
    shells=[(u,v) for A,B in groups for u in A for v in B]
    for target in range(4):
        offsets=[0]*12
        offsets[0]=target&1
        offsets[4]=target>>1
        flags=biclique_dual_witness(cols,target,groups)
        assert flags is not None
        for word in product((0,1),repeat=11):
            failures=tuple(word[u]^word[v]^d for (u,v),d in zip(endpoints,offsets))
            if failures==tuple(flags):
                assert all(not(failures[i] and failures[j]) for i,j in shells)
                break
        else:
            raise AssertionError('no original geometric assignment realizes returned flags')


def main():
    theta()
    # x implies y, y implies z, and xz=0: all dual solutions have x=0.
    # The three different quadratic monomials prevent linear cancellation.
    assert certify([([1],[3]),([2],[6]),([1],[4])])==({0},{0,1})
    # One favored orientation alone would falsely certify direction 1.
    assert certify([([1,2],[2,4])])==({0,2},{0,2})
    assert certify([])==({0},{0})
    flag_checks([1,2,4], [((0,1),(2,))],3)
    flag_checks([0,2,2], [((),(0,)),((1,),())],3)
    rng=Random(6678)
    for _ in range(90):
        rank=rng.randrange(1,5)
        count=rng.randrange(9)
        cols=[rng.randrange(1<<rank) for _ in range(count)]
        groups=[]
        j=0
        while j<count:
            k=min(count,j+rng.randrange(1,5))
            m=rng.randrange(j,k+1)
            if rng.randrange(4): groups.append((tuple(range(j,m)),tuple(range(m,k))))
            j=k
        certify([([cols[i] for i in A],[cols[i] for i in B]) for A,B in groups])
        flag_checks(cols,groups,rank)
    print('90 random exhaustive instances, four physical theta targets and strict certificate gap')


if __name__=='__main__':main()
