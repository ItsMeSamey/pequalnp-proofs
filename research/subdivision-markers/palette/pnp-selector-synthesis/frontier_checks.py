from random import Random
from frontier import solve,intersection,basis
from witness_tests import span,trace
from recognizer import tag_at
def main():
    rng=Random(91874)
    for _ in range(50):
        a=[rng.randrange(32) for _ in range(4)]
        b=[rng.randrange(32) for _ in range(3)]
        assert span(intersection(a,b))==span(a)&span(b)
    for n in range(7):
        for trial in range(16):
            d=trial%4
            cols=[(rng.randrange(1<<d),rng.randrange(4),rng.randrange(4)) for _ in range(9)]
            enc=[{m for m in range(1<<n) if rng.randrange(10)==0} for _ in range(2*d)]
            truth=set()
            for b in range(1<<n):
                chart=sum((sum(m&b==m for m in f)%2)<<i for i,f in enumerate(enc))
                ids=[i for i,(k,t,h) in enumerate(cols) if tag_at(chart,k,d)==t]
                if trace(cols,ids)==set(range(4)):truth.add(b)
            found,bounds=solve(cols,d,n,enc)
            assert bool(truth)==(found is not None)
            if found: assert found[0] in truth and trace(cols,found[1])==set(range(4))
            assert all(count<=1<<(rho+w*w+w) for rho,w,count in bounds)
    # Whole cube as a support union family; each independent block immediately expires.
    n=50
    cols=[(1<<i,t,0) for i in range(n) for t in range(4)]
    cols += [(1,1,1),(2,1,2)]
    enc=[[1<<i] for i in range(n)]+[[] for i in range(n)]
    found,bounds=solve(cols,n,n,enc)
    assert found and found[0]&3==3 and max(count for _,_,count in bounds)<=4
    print('112 literal chart images, 50 intersections and 2^50 cube / ≤4-state search passed')
if __name__=='__main__':main()
