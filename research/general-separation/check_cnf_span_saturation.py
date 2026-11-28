"""Saturation oracle from exhaustive original assignment columns."""
from itertools import combinations,product
from cnf_binary_span_saturation import project,solve,count


def valid(c,s):
    return any((abs(l) in s)==(l>0) for l in c)


def inspect(n,raw):
    names=sorted({abs(l) for row in raw for l in row})
    cube=[frozenset(v for v,b in zip(names,bits) if b)
          for bits in product(range(2),repeat=len(names))]
    models={s for s in cube if all(valid(row,s) for row in raw)}
    canonical={frozenset(row) for row in raw if not any(-l in row for l in row)}
    bg={r for r in canonical if len(r)<=2}
    residual=canonical-bg
    candidates={frozenset(sign*v for sign,v in zip(signs,vs))
                for d in (0,1,2) for vs in combinations(names,d)
                for signs in product((-1,1),repeat=d)}
    actual=project(n,raw)
    ranks=[]
    batches=[]
    while True:
        live=[s for s in cube if all(valid(r,s) for r in bg)]
        def miss(row):
            return sum(1<<i for i,s in enumerate(live) if not valid(row,s))
        span={0}
        for r in residual:
            col=miss(r)
            span|={x^col for x in span}
        ranks.append(len(span).bit_length()-1)
        if not live or len(span)==1:
            break
        accepted={r for r in candidates if miss(r) and miss(r) in span}
        if frozenset() in accepted:
            accepted={frozenset()}
        if not accepted:
            break
        assert len(batches)<len(actual.rounds)
        found=actual.rounds[len(batches)]
        assert {miss(r) for r in found}=={miss(r) for r in accepted}
        assert {frozenset(r) for r in found}==accepted
        batches.append(accepted)
        bg|=accepted
        assert {s for s in cube if all(valid(r,s) for r in bg|residual)}==models
    assert tuple(ranks)==actual.ranks and len(batches)==len(actual.rounds)
    assert all(a>b for a,b in zip(ranks,ranks[1:]))
    for fn in (solve,count):
        result=fn(n,raw)
        assert result['status']==('nonzero' if models else 'zero')
        if models:
            assert frozenset(result['true_ids']) in models
        if fn==count:
            assert result['count']==(len(models),n-len(names))
            removed=set(result['feedback_vertices'])
            assert len(removed)==result['feedback']
            edges={tuple(sorted(abs(i) for i in r)) for r in bg if len(r)==2}
            edges={e for e in edges if not (set(e)&removed)}
            while edges:
                vertices=set().union(*map(set,edges))
                leaves={v for v in vertices if sum(v in e for e in edges)==1}
                assert leaves or not actual.basis.feasible
                if not leaves:
                    break
                edges={e for e in edges if not (set(e)&leaves)}
    return ranks,len(models)


if __name__=='__main__':
    chain=[(1,2,5),(1,2,-5),(1,-2,3),(1,-3,4)]
    assert inspect(5,chain)==([4,2,1,0],18)
    full=[tuple(-v if m>>(v-1)&1 else v for v in (1,2,3)) for m in range(8)]
    assert inspect(3,full)==([8,0],0)
    assert inspect(2,[(1,),(-1,)])==([0],0)
    assert inspect(3,[(1,), (1,2,3)])==([0],4)
    assert inspect(3,[(1,2,3)])==([1],7)
    huge=1<<300
    inspect(huge,[(1,huge,4),(1,huge,-4),(1,-huge,2)])
    print('All short miss columns, three strict rounds, raw counts and sparse lifts passed.')
