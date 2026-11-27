from random import Random
from math import prod
from padded_grid_intermediate import grid_chart,partition,count
from check_padded_planar_solver import build
from check_padded_intermediate import distribution


if __name__=='__main__':
    rng=Random(481)
    for L in (2,3,4):
        perm=rng.sample(range(1,L*L+1),L*L)
        E=[tuple(sorted((perm[i],perm[j]))) for i in range(L*L)
           for j in (i+1,i+L) if j<L*L and (j==i+L or i//L==j//L)]
        side,chart=grid_chart(E,set(perm))
        signed={e:[rng.choice((-2,-1,1,2)) for _ in range(4)] for e in E}
        expected=sum(prod(f[((x>>(u-1))&1)+2*((x>>(v-1))&1)] for (u,v),f in signed.items())
                     for x in range(1<<(L*L)))
        assert partition(side,chart,signed)==expected
        if L==2:
            n,base,blocks,rows=build(E,1)
            checks=[7,3,4]
            expected=distribution(n,base,blocks,rows,checks)
            for rhs in range(8):
                answer,meta=count(n,rows,checks,rhs,budget=100000)
                assert answer==expected.get(rhs,0)
                if meta['status']=='counted':
                    assert count(n,rows,checks,rhs,budget=meta['bound']-1)[0] is None
    E=[(1,2),(2,3),(3,4),(4,1),(1,3)]
    assert grid_chart(E,{1,2,3,4}) is None
    print('signed relabeled grid partitions L=2,3,4, eight original syndrome fibers, chord rejection and cap skips passed')
