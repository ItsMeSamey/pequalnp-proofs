import random
from sparse_decision import solve,Limit
from cover import direct


def main():
    rnd=random.Random(55175)
    for _ in range(800):
        n,m=rnd.randrange(1,6),rnd.randrange(0,8)
        g=[tuple(rnd.randrange(2<<(n+i)) for _ in range(3)) for i in range(m)]
        out=rnd.randrange(2<<(n+m))
        pins=rnd.randrange(1<<n)
        values=rnd.randrange(1<<n)&pins
        exists=any(direct(n,g,out,x) for x in range(1<<n) if x&pins==values)
        for peel in (True,False):
            w,_=solve(n,g,out,8192,10**7,pins,values,peel)
            assert (w is not None)==exists
    for k in [8,24,80]:
        # Connected chain accepting iff x0*x1*x2=1 and all later inputs are zero.
        n=k+3
        g=[(2,4,0),(2<<(n+0),8,0)]
        for j in range(k):
            g.append((2<<(n+len(g)-1),1^(2<<(j+3)),0))
        out=2<<(n+len(g)-1)
        w,used=solve(n,g,out,8,100000)
        assert w==7
        try:
            solve(n,g,out,8,100000,peel=False)
        except Limit:
            pass
        else:
            raise AssertionError('uncapped route unexpectedly fits')
        print(k,w,used)
    print('800 originals both modes with pins passed')


if __name__=='__main__':
    main()
