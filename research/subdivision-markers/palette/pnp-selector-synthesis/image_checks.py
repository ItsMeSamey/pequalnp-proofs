from image_solver import solve
from random import Random
from witness_tests import trace
from recognizer import tag_at
def main():
    rng=Random(721)
    for n in range(5):
        for case in range(10):
            cols=[(1,0,0),(2,2,1)]+[(rng.randrange(4),rng.randrange(4),rng.randrange(4)) for _ in range(5)]
            enc=[{m for m in range(1<<n) if rng.randrange(5)==0} for _ in range(4)]
            valid=set()
            for b in range(1<<n):
                g=sum((sum(m&b==m for m in f)%2)<<i for i,f in enumerate(enc))
                ids=[i for i,(k,t,h) in enumerate(cols) if tag_at(g,k,2)==t]
                if trace(cols,ids)==set(range(4)): valid.add(b)
            _,found=solve(cols,2,n,enc,[(2,0),(3,2)])
            assert (found is not None)==bool(valid)
            if found: assert found[0] in valid and trace(cols,found[1])==set(range(4))
    host=[(1,t,0) for t in range(4)]+[(1,1,1),(0,0,2)]
    for n in range(1,9):
        _,found=solve(host,1,n,[[(1<<n)-1],[]],[(2,0)])
        assert found[0]==(1<<n)-1
    print('50 full chart-image comparisons and 8 singleton AND controls passed')
if __name__=='__main__': main()
