from collections import Counter
from itertools import product
from random import Random
from three import select


def add(xs):
    result=0
    for x in xs: result^=x
    return result


def span(xs):
    S={0}
    for x in xs:S |= {s^x for s in S}
    return S


def score(tags,f,g):
    return add((a if f>>i&1 else 0)^(b if g>>i&1 else 0) for i,(a,b) in enumerate(tags))


def valid(cols,f,g):
    zeros=[c for i,c in enumerate(cols) if not ((f|g)>>i & 1)]
    return (not add(x for i,x in enumerate(cols) if f>>i & 1)
            and not add(x for i,x in enumerate(cols) if g>>i & 1)
            and len(span(zeros))==1<<len(zeros))


def all_scores(cols,tags):
    words=[s for s in range(1<<len(cols)) if not add(c for i,c in enumerate(cols) if s>>i & 1)]
    return {score(tags,f,g) for f,g in product(words,repeat=2) if valid(cols,f,g)}


def run():
    rng=Random(17351)
    counts=Counter()
    cases=[]
    for i in range(700):
        d=rng.randrange(5)
        m=rng.randrange(8)
        if d==0:m=min(m,4)
        cols=[rng.randrange(1<<d) for _ in range(m)]
        tags=[(rng.randrange(8),rng.randrange(8)) for _ in cols]
        cases.append((cols,tags))
    for i in range(1300):
        r=rng.randrange(5)
        h=rng.randrange(2,5)
        cols=[1<<j for j in range(r)]+[rng.randrange(1<<r) for _ in range(h)]
        tags=[(0,0)]*r
        if i%2:
            tags += [(1,2),(1,4)] + [(0,0)]*(h-2)
        else:
            tags += [(1,2)]+[(rng.choice((0,4)),rng.choice((0,4))) for _ in range(h-1)]
        cases.append((cols,tags))
    for tags in product(((0,0),(1,2),(1,4),(2,4),(3,6)),repeat=2):
        cases.append((list(range(1,8)),[(0,0)]*5+list(tags)))
    for cols,tags in cases:
        expected=all_scores(cols,tags)
        for t in range(8):
            found,why=select(cols,tags,t)
            assert (found is not None)==(t in expected),(cols,tags,t,why,found,expected)
            if found is not None:
                assert valid(cols,*found) and score(tags,*found)==t
            counts[why]+=1
    print(len(cases),'matrices;',dict(counts))
    assert all(counts[name] for name in ('one forced','one spread','two spread','two split yes','two split no'))
run()
