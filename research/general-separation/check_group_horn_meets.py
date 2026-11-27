"""Independent orientation oracle uses meet closure of each allowed truth table."""
from itertools import product
from ring_image_group_horn import solve_tuples,solve_sparse,decide
from read_two_ring_nonzero import compile_nonzero


def oracle(groups):
    labels=sorted({i for scope,_ in groups for i in scope})
    full=set(range(1<<len(labels)))
    sets={}
    for scope,bad in groups:
        forbidden=set(bad)
        allowed={w for w in full if sum((w>>labels.index(v)&1)<<j
                                        for j,v in enumerate(scope)) not in forbidden}
        key=tuple(sorted(scope))
        sets[key]=sets.get(key,full)&allowed
    orientations=[]
    for f in full:
        if all(all((((x^f)&(y^f))^f) in s for x in s for y in s) for s in sets.values()):
            orientations.append(f)
    models=full.intersection(*sets.values())
    ans=solve_tuples(groups)
    if not orientations:
        assert ans['status']=='unknown'
    else:
        assert ans['status']==('nonzero' if models else 'zero')
        assert sum(1<<labels.index(v) for v in ans['flips']) in orientations
        if models:
            assert sum(ans['assignment'][v]<<j for j,v in enumerate(labels)) in models


def main():
    for mask in range(256):
        oracle([((8,2,5),[x for x in range(8) if mask>>x&1])])
    for first,second in product(range(16),repeat=2):
        oracle([((1,2),[x for x in range(4) if first>>x&1]),
                ((2,3),[x for x in range(4) if second>>x&1]),
                ((2,1),[0])])
    big=1<<1000
    ans=solve_sparse([(big,),(-big,7)],labels=(11,))
    assert ans['assignment'][big]==ans['assignment'][7]==1 and 11 in ans['assignment']
    for rows,wanted in [([(1,),(-1,3)],'nonzero'), ([(1,),(-1,)],'zero'),
                        ([tuple(-i if x>>(i-1)&1 else i for i in range(1,4))
                          for x in (1,2,4,7)],'unknown')]:
        r=compile_nonzero(3,rows)
        args=[r[k] for k in ('n','clauses','point','k')]
        ans=decide(*args)
        assert ans['status']==wanted
        if wanted=='nonzero':
            assert all(any(ans['assignment'][abs(v)-1]==(v>0) for v in c) for c in rows)
        args[-1]+=1<<1000
        assert decide(*args)['status']=='off_image'
    print('512 meet-closure comparisons, sparse labels and physical image verdicts passed.')


if __name__=='__main__':
    main()
