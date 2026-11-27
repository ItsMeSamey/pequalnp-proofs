"""Raw four-field image decisions vs exhaustive source bits, independently of ring sums."""
from itertools import combinations, product
from read_two_ring_nonzero import compile_nonzero
from ring_image_clique_matching import decide as matching
from ring_image_existential import decide as eliminate


def image(n,cs):
    r=compile_nonzero(n,cs)
    return tuple(r[k] for k in ('n','clauses','point','k'))


def truth(n,cs):
    return {v for v in product(range(2),repeat=n)
            if all(any(v[abs(l)-1]==(l>0) for l in row) for row in cs)}


def verify(r,models):
    assert r['status']==('nonzero' if models else 'zero'),r
    if models:
        assert tuple(r['assignment']) in models


def main():
    # Edges of the 3-crown with a permutation of variable names.
    edges=[(i,j) for i,j in product(range(3),repeat=2) if i!=j]
    names=[5,1,6,3,2,4]
    stars=[tuple(v for v,e in zip(names,edges) if e[side]==i)
           for side,i in product(range(2),range(3))]
    conflicts=[(-a,-b) for row in stars for a,b in combinations(row,2)]
    for cs in [stars+conflicts, stars+conflicts+[(names[0],),(names[1],)]]:
        verify(matching(*image(6,cs)),truth(6,cs))
    foil=[(1,2),(3,),(-1,-3),(-2,-3)]
    assert not truth(3,foil)
    assert matching(*image(3,foil))==dict(status='unknown',reason='nonclique')
    for rows in [[(3,),(-3,1),(-1,2)],[(3,),(-3,1),(-1,2),(-2,)],
                 [(1,-1),(3,2)], [()], []]:
        data=image(3,rows)
        verify(eliminate(*data,max_rows=32),truth(3,rows))
    assert eliminate(*image(1,[(1,)]),max_rows=0)==dict(status='unknown',reason='row_budget')
    from ring_image_frontier import solve as frontier
    # At x1=0 the residual demands both polarities of x2. At x1=1 only
    # x2 remains constrained. Keeping just the stronger branch loses the model.
    for rows in [[(1,-2),(2,)], [(-1,2), (1,-2)], [(-3,1),(-1,2),(3,),(-2,)],
                 [(3,2),(2,3),(-1,-2),(1,3)], [], [()]]:
        raw=image(3,rows)
        verify(frontier(*raw,max_states=16),truth(3,rows))
    refusal=frontier(*image(2,[(-1,2),(1,-2)]),max_states=0)
    assert refusal['status']=='unknown' and refusal['reason']=='state_budget'
    assert refusal['available']==0 and refusal['required']>=1
    nv,c,p,k=image(1,[(1,)])
    for solver in (eliminate,matching,frontier):
        assert solver(nv,c,p,k+(1<<1000))['status']=='off_image'
    print('Crown, nonclique, implications, resource limits and physical source witnesses passed.')


if __name__=='__main__':
    main()
