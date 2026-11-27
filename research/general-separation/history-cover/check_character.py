from random import Random
from cover import System, direct
from bank import compress
from character_backend import backend, Unsupported


def main():
    rng=Random(19484)
    checked=0
    for _ in range(300):
        n=rng.randrange(2,6)
        m=rng.randrange(1,6)
        g=[tuple(rng.randrange(2<<(n+i)) for _ in range(3)) for i in range(m)]
        out=rng.randrange(2<<(n+m))
        s,_=compress(n,g,out,m,stages=m)
        counter=backend(s,8)
        for pins in range(1<<n):
            assignment=rng.randrange(1<<n)&pins
            assert counter(s,pins,assignment)==sum(direct(n,g,out,x) for x in range(1<<n) if x&pins==assignment)
        if counter.rank:
            try:
                backend(s,counter.rank-1)
            except Unsupported:
                pass
            else:
                raise AssertionError('ignored rank budget')
        checked+=1
    s=System(3,[(16,[(2,4)]),(32,[(2,8)]),(64,[(2,4),(2,8),(4,)])],[(16^32^64,)])
    c=backend(s,2)
    assert c.rank==2 and c(s,0,0)==4
    # Encode any 3CNF using two product gates per clause and product accumulator.
    n=9
    clauses=[(i,(i+1)%n,(i+3)%n) for i in range(n)]
    g=[]
    acc=1
    for j,(a,b,cvar) in enumerate(clauses):
        u=(2<<a)^(j&1)
        v=(2<<b)^((j>>1)&1)
        w=(2<<cvar)^((j>>2)&1)
        z=2<<(n+len(g))
        g.extend([(u,v,0),(z,w,1),(acc,z<<1,0)])
        acc=z<<2
    s,_=compress(n,g,acc,len(g),stages=len(g))
    try:
        backend(s,2)
    except Unsupported:
        pass
    else:
        raise AssertionError('3CNF control unexpectedly passed budget')
    print('300 random circuits, all pin masks; shared dependent quadratic and mixed 3CNF refusal passed')


if __name__=='__main__':
    main()
