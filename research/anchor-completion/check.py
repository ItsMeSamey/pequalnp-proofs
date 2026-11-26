from itertools import product
from random import Random
from solver import count,completion,par

def brute(ms,c,ls):
    out={}
    for x in range(1<<len(ms)):
        if any((x>>i&1) and par(x&m)!=(c>>i&1) for i,m in enumerate(ms)):continue
        p=0
        for i,l in enumerate(ls):
            if x>>i&1:p^=l
        out[p]=out.get(p,0)+1
    return out
rng=Random(670)
for n in range(9):
    for _ in range(70):
        t=rng.randrange(4)
        ms=[rng.randrange(1<<n) for i in range(n)]
        labels=[rng.randrange(1<<t) for _ in range(n)]
        offset=rng.randrange(1<<n)
        d,out=count(ms,offset,labels,t)
        assert out==brute(ms,offset,labels)
for _ in range(300):
    nr=rng.randrange(1,6); nc=rng.randrange(1,8)
    pairs=[]
    for i in range(nc):
        x=rng.randrange(1<<nr)
        pairs.append((x,x^(1<<rng.randrange(nr))))
    cols,w=completion(pairs)
    def dim(vs):
        space={0}
        for v in vs:space|={s^v for s in space}
        return len(space).bit_length()-1
    assert len(cols)==min(map(dim,product(*pairs)))
print('630 guard counting instances and 300 minimum-completion checks passed.')
