"""Independently compare native contraction masks, zero forests and gains."""
from itertools import combinations
from random import Random
from selector import Instance, basis_indices, canonical, eliminate, image, positions, solve
from router import route_forest, brute_linkage


def all_trees(I):
    return [sum(1<<i for i in ids) for ids in combinations(range(I.m),I.tree.bit_count())
            if len(basis_indices(I.D,ids))==len(ids)]


def raw_root(I):
    """Arbitrary contraction masks, no presumed pattern inside a block."""
    shift=I.m+2*I.n
    cols=[]
    for e in range(I.m):
        for s in range(1,4):
            a,b=I.edges[e]
            v=1<<e
            for h in range(2):
                if s>>h&1:
                    v ^= ((1<<a)^(1<<b))<<(I.m+h*I.n)
                    v ^= ((I.tags[e]>>(I.k*h))&I.mask)<<shift
            cols.append(v)
    targets=set()
    tags=tuple(1<<(shift+j) for j in range(I.k))
    for mask in range(1<<len(cols)):
        if any(mask>>(3*i)&7==0 for i in range(I.m)):
            continue
        chosen=canonical(cols[i] for i in positions(mask))
        if len(canonical(chosen+tags))!=len(chosen)+I.k:
            continue
        for t in range(1<<I.k):
            if solve(chosen,I.full|(t<<shift)) is not None:
                targets.add(t)
    return targets


def run():
    rng=Random(987123)
    stats=dict(graphs=0,targets=0,raw_targets=0,routings=0,flows=0,certificates=0)
    for rep in range(80):
        n=rng.randrange(1,6)
        m=rng.randrange(0,6)
        k=rep%5
        edges=[(rng.randrange(n),rng.randrange(n)) for _ in range(m)]
        tags=[(rng.randrange(1<<k),rng.randrange(1<<k)) for _ in edges]
        I=Instance(n,edges,tags,k)
        trees=all_trees(I)
        X={t for tree in trees for t in I.chord_targets(image(I.tags,c) for c in I.fundamental(tree).values())}
        brute=set()
        C=[s for s in range(1<<m) if image(I.D,s)==0]
        for f in C:
            for g in C:
                Z=list(positions(I.full^(f|g)))
                if len(basis_indices(I.D,Z))==len(Z):
                    brute.add(image([a for a,b in tags],f)^image([b for a,b in tags],g))
        assert X==brute
        if m<=3:
            assert raw_root(I)==X
            stats['raw_targets']+=1<<k
        def oracle(I,J):
            for tree in trees:
                cycles=I.fundamental(tree)
                if all(e in cycles and image(I.tags,cycles[e])==x for e,x in J.items()):
                    return tree
            return None
        for t in range(1<<k):
            flow=I.solve_fixed(t,oracle)
            if k<=2:
                local=I.solve_two(t)
                assert (local is not None)==(t in X)
                if local is not None:
                    assert I.physical(t,local)[1]==(1,)
            assert (flow is not None)==(t in X)
            if flow is not None:
                assert I.physical(t,flow)[1]==(1,)
                stats['flows']+=1
            stats['targets']+=1
        for tree in trees:
            keep,S,H=I.finite_certificate(tree)
            for alt in trees:
                cycles=I.fundamental(alt)
                if all(e in cycles and image(I.tags,cycles[e])==x for e,x in keep.items()):
                    assert S==I.chord_targets(image(I.tags,c) for c in cycles.values())
                    stats['certificates']+=1
        if k<=2:
            cycles=I.fundamental(rng.choice(trees))
            keys=list(cycles)[:2]
            for flip in (False,True):
                J={j:image(I.tags,cycles[j]) for j in keys}
                if flip and keys and k:
                    J[keys[0]] ^= 1
                assert (route_forest(I,J,brute_linkage) is None)==(oracle(I,J) is None)
                stats['routings']+=1
        stats['graphs']+=1
    # Three marked fundamental paths meeting at an unmarked degree-three vertex.
    star=Instance(4,[(0,1),(0,2),(0,3),(1,2),(2,3),(3,1)],
                  [(1,0),(0,1),(1,1),(0,0),(0,0),(0,0)],1)
    J={e:image(star.tags,c) for e,c in star.fundamental(7).items()}
    assert route_forest(star,J,brute_linkage)==7
    # Source controls. Compare physical selectors with strict nowhere-zero flows.
    graphs=[(4,list(combinations(range(4),2)),True),
            (6,[(i,j) for i in range(3) for j in range(3,6)],True),
            (10,[(i,(i+1)%5) for i in range(5)]+[(5+i,5+(i+2)%5) for i in range(5)]
             +[(i,i+5) for i in range(5)],False)]
    controls=[]
    for n,edges,colorable in graphs:
        I=Instance(n,edges,[(1,2)]*len(edges),2)
        B=tuple(I.fundamental(I.tree).values())
        C=[image(B,i) for i in range(1<<len(B))]
        strict=sum((f|g)==I.full for f in C for g in C)
        assert bool(strict)==colorable
        attainable=[t for t in range(4) if I.solve_two(t) is not None]
        controls.append((n,strict,attainable))
    assert 0 in controls[-1][2]
    print(stats)
    print('K4, K3,3, Petersen (order, strict labelled flow count, native targets)',controls)


if __name__=='__main__':
    run()
