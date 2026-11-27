"""Ground truth via unsigned distributions of actual local raw-clause violations."""
from collections import Counter
from check_padded_planar_solver import build
from padded_intermediate import count


def distribution(n,base,blocks,rows,checks):
    index={c:i for i,c in enumerate(rows)}
    full=Counter()
    for x in range(1<<base):
        freq={0:1}
        for private,block in blocks:
            local=Counter()
            for y in range(1<<len(private)):
                word=x|sum(((y>>j)&1)<<(v-1) for j,v in enumerate(private))
                violation=sum(1<<index[c] for c in block if not any(bool(word>>(abs(l)-1)&1)==(l>0) for l in c))
                signature=sum(((violation&s).bit_count()%2)<<j for j,s in enumerate(checks))
                local[signature]+=1
            nxt=Counter()
            for a,v in freq.items():
                for b,w in local.items(): nxt[a^b]+=v*w
            freq=nxt
        full.update(freq)
    free=n-base-sum(len(p) for p,_ in blocks)
    return {a:v<<free for a,v in full.items()}


if __name__=='__main__':
    tests=0
    for E in [[(1,2),(2,3),(1,3)],[(1,2),(2,3),(3,4),(4,1),(1,3)]]:
        n,base,blocks,rows=build(E,1)
        for checks in [(),(0,), (1,), (3,6,5),(1,1),(0,7,15)]:
            expect=distribution(n,base,blocks,rows,checks)
            for rhs in range(1<<len(checks)):
                v,meta=count(n,rows,checks,rhs,budget=100000)
                assert v==expect.get(rhs,0),(checks,rhs,v,expect)
                if meta['status']=='counted':
                    assert count(n,rows,checks,rhs,budget=meta['bound']-1)[0] is None
                tests+=1
        assert count(n,rows,(),budget=100000)[0]==1<<n
    print(tests,'original signed-CNF intermediate syndrome fibers, empty/overlap/duplicate/inconsistent checks and budget skips passed')
