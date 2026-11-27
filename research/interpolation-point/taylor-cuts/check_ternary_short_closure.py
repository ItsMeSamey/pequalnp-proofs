from itertools import product
from random import Random
from ternary_short_closure import close

def models(n,rows):
    return {s for s in product((1,2),repeat=n)
            if not any(sum(x*y for x,y in zip(row,s))%3 for row in rows)}

def check(n,local,glob):
    expected = models(n,local+glob)
    q = close(n,local,glob)
    if q is None:
        assert not expected
    else:
        actual={q.lift(s) for s in models(q.n,q.local+q.global_rows)}
        assert actual==expected
    return q

if __name__=='__main__':
    q=check(8,[],[[1]*8,[2,2,2,1,1,1,1,1]])
    assert q.n==6
    assert check(8,[],[[1]*8,[2,1,1,1,1,1,1,1]]) is None
    q=check(8,[[1]*4+[0]*4,[0]*4+[1]*4],[[1]*8])
    assert len(q.local)==2 and not q.global_rows
    rng=Random(661)
    for j in range(250):
        n=rng.randrange(8)
        rows=[[rng.randrange(3) for i in range(n)] for k in range(rng.randrange(9))]
        p=rng.randrange(len(rows)+1)
        check(n,rows[:p],rows[p:])
    print('253 exact model-set comparisons passed')
