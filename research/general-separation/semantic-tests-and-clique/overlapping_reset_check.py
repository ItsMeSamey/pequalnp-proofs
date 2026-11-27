"""Exhaust guard resets and prefix-cylinder bounds on small unate hypergraphs."""
from fractions import Fraction
from random import Random


def guards(n,edges):
    result=[]
    for j in range(n):
        v=1<<j
        if v in edges:continue
        block=v
        for e in edges:
            if e&v:
                above=e&~((v<<1)-1)
                nextbit=(above&-above) if above else e&-e
                block|=nextbit
        result.append((block,v))
    return result


def mask(x,edges):
    return sum((x&e==e)<<i for i,e in enumerate(edges))


def holder(count,total,events,n):
    # Avoidance raised to degree d is at most product of marginal avoidances.
    if not events:
        assert count==total
        return
    d=max(1,max(sum(bool(b>>i&1) for b,v in events) for i in range(n)))
    bound=Fraction(1)
    for b,v in events:bound*=1-Fraction(1,1<<b.bit_count())
    assert Fraction(count,total)**d<=bound


def check(n,edges,check_prefix=True):
    gs=guards(n,edges)
    good=[]
    for x in range(1<<n):
        y=x
        for step in range(n+1):
            triggers=[v for b,v in gs if y&b==v]
            if not triggers:break
            assert all(mask(y,edges)==mask(y^v,edges) for v in triggers)
            y^=triggers[0]
        assert step<=n and mask(x,edges)==mask(y,edges)
        if y==x:good.append(x)
    assert {mask(x,edges) for x in good}=={mask(x,edges) for x in range(1<<n)}
    if check_prefix:
        for k in range(n+1):
            pre=(1<<k)-1
            prefixes={x&pre for x in good}
            finished=[(b,v) for b,v in gs if not b&~pre]
            possible=[s for s in range(1<<k) if all(s&b!=v for b,v in finished)]
            assert prefixes<=set(possible)
            holder(len(possible),1<<k,finished,n)
            for s in range(1<<k):
                rem=[(b&~pre,v&~pre) for b,v in gs if s&(b&pre)==v&pre]
                holder(sum(x&pre==s for x in good),1<<(n-k),rem,n)
    return len(good)


if __name__=='__main__':
    for d in range(2,6):
        edges=[1<<i|1<<(d+j) for i in range(d) for j in range(d)]
        expected=1+((1<<d)-1)**2
        assert check(2*d,edges)==expected
        print('K',d,d,'canonical masks',expected)
    tri=[7]
    assert guards(3,tri)==[(3,1),(6,2),(5,4)]
    assert [v for b,v in guards(3,tri) if 3&b==v]==[2]
    assert [v for b,v in guards(3,tri) if 1&b==v]==[1]
    rng=Random(3283)
    for _ in range(35):
        n=rng.randrange(1,8)
        check(n,[rng.randrange(1<<n) for _ in range(rng.randrange(10))])
    print('35 hypergraphs and reset cascade 011 -> 001 -> 000 passed')
