"""Exact forced mixed-terminal placements, followed by a permissive sink bank."""
from collections import Counter
from functools import reduce
from itertools import combinations,combinations_with_replacement
from operator import or_
from h5_three_sink_leak_sets import EDGES,N,CASES
from h5_prefix_nine_bank import indices,singletons,edge_bits

def submasks(mask):
    s = mask
    while s:
        yield s
        s=(s-1)&mask

def placements(ix):
    i,j=CASES[ix]
    c1,c2=1023^N[i],1023^N[j]
    common=c1 & c2
    assert common.bit_count()==5
    for y in submasks(common):
        if y.bit_count()!=4:
            continue
        choices=[]
        for cover in (c1,c2):
            choices.append([a for a in submasks(cover) if (a|y)==cover
                            and 2<=a.bit_count()<=3 and (a&y).bit_count()<=1])
        for a in choices[0]:
            for b in choices[1]:
                if (a&b).bit_count()>1:
                    continue
                for d in range(1,1024):
                    if sorted(s.bit_count() for s in (a,b,y,d))!=[2,3,3,4]:
                        continue
                    if any((d&s).bit_count()>1 for s in (a,b,y)):
                        continue
                    # Hidden H here denotes the product in U. Both chronological
                    # orders are physically equivalent since all four scopes are raw.
                    yield a,b,y,d

def passes(scopes,ix):
    a,b,y,d=scopes
    bank=set(singletons)
    for s in scopes:
        bank.update(submasks(s))
    bank.add(y|1024)
    rows=[w|(1024 if w&a and w&b else 0)|(2048 if w&y and w&d else 0) for w in (*EDGES,*N)]
    wanted=edge_bits|sum(1<<(len(EDGES)+i) for i in CASES[ix])
    traces={sum(1<<i for i,w in enumerate(rows) if s&w) for s in bank}
    legal={u&v for u,v in combinations_with_replacement(traces,2)
           if not (u&v)&~wanted and (u&v)&edge_bits and (u&v)&~edge_bits}
    if reduce(or_,legal,0)!=wanted:
        return False
    maximal=[s for s in legal if not any(t!=s and (s&t)==s for t in legal)]
    return any((a|b|c)==wanted for a,b,c in combinations_with_replacement(maximal,3))

if __name__=='__main__':
    for mask in (973,907,905,904,0,7,512):
        assert set(submasks(mask))=={s for s in range(1,1024) if s & mask == s}
    for ix in indices:
        candidates=list(placements(ix))
        print(ix,len(candidates),sum(passes(s,ix) for s in candidates),flush=True)
