from random import Random


def image(cols, x):
    ans=0
    for i,v in enumerate(cols):
        if x>>i&1: ans^=v
    return ans


def bit(a,b):
    return (a&b).bit_count()%2


if __name__=='__main__':
    rng=Random(7183)
    checks=0
    for _ in range(2000):
        m=rng.randrange(2,10)
        s=1<<m
        t=s-1
        a,bz,bw=[rng.randrange(s) for _ in range(3)]
        left=bz&~bw
        right=bw&~bz
        if not left or not right:continue
        # The first m positions represent C minus t, followed by root and two chords.
        cols=[1<<i for i in range(m)]+[t,s^bz,s^bw]
        b=rng.randrange(2)
        q=b*s^a
        ell=rng.randrange(1<<(m+3))
        C=(1<<(m+1))-1
        X=(C^(bz^bw))|(3<<(m+1))
        assert image(cols,X)==0 and X&s
        dh=bit(ell,bz^bw)^bit(ell,3<<(m+1))
        for e in range(m):
            for f in range(m):
                if not (left>>e&1 and right>>f&1):continue
                d=s^(1<<e)^(1<<f)
                assert bit(d,s) and all(not bit(d,v) for i,v in enumerate(cols) if X>>i&1)
                assert bit(d,q)^b==bit(a,(1<<e)|(1<<f))
                assert bit(ell,X)^bit(ell,C)==dh
                checks+=1
    print(checks,"explicit two-column exchanges verified")
