from random import Random
from gram_pass_rail import count_passes


def check(n,size,passes,order):
    counts=[]
    for x in range(1<<n):
        live=[]
        for s in range(size):
            t=s
            for _,gates in passes:
                for v,p,q in gates:
                    b=(x>>(abs(v)-1)&1)^(v<0)
                    t=(q if b else p)[t]
            if s==t:live.append(s)
        counts.append(live)
    total,w,r=count_passes(n,size,passes,order)
    assert total==sum(map(len,counts))
    assert (w[1] in counts[w[0]]) if total else w is None
    return r


if __name__=='__main__':
    rng=Random(393)
    for _ in range(60):
        n=rng.randrange(1,5);size=rng.randrange(2,5)
        order=list(range(1,n+1));rng.shuffle(order)
        passes=[]
        for j in range(rng.randrange(4)):
            forward=rng.choice((True,False));gates=[]
            for v in order if forward else reversed(order):
                for k in range(rng.randrange(3)):
                    p=list(range(size));q=p.copy();rng.shuffle(p);rng.shuffle(q)
                    gates.append((v*rng.choice((-1,1)),p,q))
            passes.append((forward,gates))
        check(n,size,passes,order)
    n=7;order=list(range(1,n+1));e=(0,1,2)
    pass1=[(v,e,((1,0,2) if v%2 else (0,2,1))) for v in order]
    rank=check(n,3,[(True,pass1)]*9,order)
    assert rank<=6
    print(f'60 signed forward/reverse systems and a nine-pass single SCC passed; peak rank {rank}')
