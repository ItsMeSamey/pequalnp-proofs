"""Generate physical mixed-terminal placements by complement equalities."""
from collections import Counter
from functools import lru_cache
from h5_submasks import submasks
from h5_three_sink_leak_sets import EDGES, N, CASES

indices=(2,8,11,18,29,44,65,114)
rows=(*EDGES,*N)
pos=(1<<len(EDGES))-1
raw_traces=[sum(1<<i for i,row in enumerate(rows) if row & s) for s in range(1024)]
widths={k:tuple(s for s in range(1,1024) if s.bit_count()==k) for k in range(1,10)}

def linear(a,b):
    return a!=b and (a&b).bit_count()<=1

def useful(a,b):
    v=raw_traces[a]&raw_traces[b]
    return (a&b) not in (a,b) and bool(v&pos and v&~pos)

@lru_cache(maxsize=512)
def possible(a,b,width):
    return tuple(s for s in widths.get(width,()) if linear(s,a) and linear(s,b))

def candidates(ix):
    i,j=CASES[ix]
    first,second=1023^N[i],1023^N[j]
    common=first&second
    assert common.bit_count()==5
    for y in submasks(common,include_zero=False):
        if y.bit_count()<4:
            continue
        ext=tuple(submasks(y))
        for x in ext:
            a=(first^y)|x
            for z in ext:
                b=(second^y)|z
                if not linear(a,b) or not useful(a,b):
                    continue
                remain=11-a.bit_count()-b.bit_count()
                hosted=(a&y)==y or (b&y)==y
                for k in range(1,remain):
                    if not hosted and k<y.bit_count():
                        continue
                    for c in possible(a,b,k):
                        if not hosted and (c&y)!=y:
                            continue
                        for d in possible(a,b,remain-k):
                            if hosted and c>=d:
                                continue
                            if linear(c,d) and useful(c,d):
                                yield a,b,c,d,y

if __name__=='__main__':
    import sys
    ix=int(sys.argv[1])
    counts=Counter(''.join(map(str,sorted(s.bit_count() for s in q[:4]))) for q in candidates(ix))
    print(ix,sum(counts.values()),*sorted(counts.items()))
