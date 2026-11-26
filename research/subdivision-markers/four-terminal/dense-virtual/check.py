"""Exhaust coefficient identities on seeded small dense-port instances."""
from itertools import combinations
from random import Random
rng=Random(224)
def rank(cols):
    bas={}
    for v in cols:
        while v:
            i=v.bit_length()-1
            if i not in bas:
                bas[i]=v
                break
            v^=bas[i]
    return len(bas)
def minor(cols,mask):
    return int(rank([v&mask for v in cols])==len(cols))
def even(n):
    v=rng.randrange(1<<(n-1))
    return (v<<1) | (v.bit_count()%2)
cnt=0
positive=0
for trial in range(260):
    n=rng.randrange(2,8); h=rng.randrange(n); full=(1<<n)-1
    O=[(1<<rng.randrange(n))^(1<<rng.randrange(n)) for _ in range(rng.randrange(1,10))]
    W=[even(n) for _ in range(h)]
    u=even(n)
    anchors=[sum(1<<v for v in a) for a in combinations(range(n),h+1)]
    for F in combinations(O,n-1-h):
        expect=rank([*F,*W])==n-1 and rank([*F,u])==rank(F)
        got=0
        for a in anchors:
            if a&1 and minor(W,a^1) and minor(F,full^a):
                got^=sum(minor(F,full^b) for b in anchors if not b&~(u^a))%2
        assert got==expect
        cnt+=1;positive+=expect
print(cnt, 'coefficients checked;',positive,'positive')
