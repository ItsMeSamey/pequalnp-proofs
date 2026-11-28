"""Decision-only shared-hit regression from original source truth words."""
from itertools import product
from cnf_binary_background_rank import solve


def main():
    rows=[(1,a,b) for a in (-2,2) for b in (-3,3)]+[(1,4,5)]
    cube=list(product(range(2),repeat=5))
    models={v for v in cube if all(any(v[abs(i)-1]==(i>0) for i in c) for c in rows)}
    assert models=={v for v in cube if v[0]}
    r=solve(5,rows)
    assert r['rank']==5 and r['branches']==2 and r['status']=='nonzero'
    assert r['hit_variables']==(1,)
    assert tuple(int(i in r['true_ids']) for i in range(1,6)) in models
    denial=solve(5,rows,max_branches=1)
    assert denial['status']=='unknown' and denial['required']==2
    assert solve(5,rows,max_branches=2)['status']=='nonzero'
    print('Five independent ternary misses share one hit; exactly two 2-SAT branches.')


if __name__=='__main__':
    main()
