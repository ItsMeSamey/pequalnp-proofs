from random import Random
from profile_solver import solve
from witness_tests import trace

def main():
    rng = Random(115)
    for d in range(4):
        for case in range(10):
            cols=[(1<<i,rng.randrange(4),rng.randrange(4)) for i in range(d)]
            cols += [(rng.randrange(1<<d),rng.randrange(4),rng.randrange(4)) for _ in range(4)]
            expect = any(trace(cols,[i for i in range(len(cols)) if m>>i&1])==set(range(4)) for m in range(1<<len(cols)))
            for s,j in [(2,0),(2,2),(3,1)]:
                got,t,D=solve(cols,d,s,j)
                assert D<=2*j and (got is not None)==expect
                if got is not None: assert trace(cols,got)==set(range(4))
    # Each disjoint 24-site block has zero full-tag directions but degree-three
    # lifts spanning all four private axes with height zero on the original sites.
    for blocks in (1,2):
        cols=[]
        for i in range(blocks):
            for k in sorted(set(range(1,16))-{3,8,11}):
                for b in range(2):
                    tag=int(1 ^ ((k&3)==3) ^ ((k&12)==12)) | (b<<1)
                    cols.append((k<<(4*i),tag,0))
        for incompatible in (False,True):
            k,b,_=cols[0]
            k2,b2,_=cols[1 if incompatible else 2]
            physical=cols+[(k,b,1),(k2,b2,2)]
            got,t,D=solve(physical,4*blocks,3,0)
            assert t==D==0 and (got is None)==incompatible
            if got is not None: assert trace(physical,got)==set(range(4))
    print('120 literal comparisons and 4 disjoint-block separation controls passed')
if __name__=='__main__': main()
