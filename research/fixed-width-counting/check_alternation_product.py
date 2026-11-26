from functools import cache
from itertools import product
from random import Random
rng=Random(320)
def mul(a,b):
    return tuple(sum(a[2*i+k]*b[2*k+j] for k in (0,1)) for i,j in product((0,1),repeat=2))
def add(a,b):
    return tuple(x+y for x,y in zip(a,b))
def test(word,mats):
    @cache
    def boundary(i,j):
        return tuple(sorted(set(word[i:j]) & set(word[:i]+word[j:])))
    @cache
    def plan(i,j):
        if j-i==1:return 1,None
        return min((max(plan(i,k)[0],plan(k,j)[0],len(set(boundary(i,k))|set(boundary(k,j)))),k) for k in range(i+1,j))
    @cache
    def table(i,j):
        if j-i==1:
            return {(b,):mats[i][b] for b in (0,1)} if boundary(i,j) else {():add(*mats[i])}
        _,k=plan(i,j)
        X,Y,Z=boundary(i,k),boundary(k,j),boundary(i,j)
        merged=tuple(sorted(set(X)|set(Y)))
        ans={}
        for bits in product((0,1),repeat=len(merged)):
            a=dict(zip(merged,bits))
            z=tuple(a[v] for v in Z)
            pair=mul(table(i,k)[tuple(a[v] for v in X)],table(k,j)[tuple(a[v] for v in Y)])
            ans[z]=add(ans.get(z,(0,)*4),pair)
        return ans
    out=(0,)*4
    for vals in product((0,1),repeat=max(word)+1):
        t=(1,0,0,1)
        for i,v in enumerate(word):t=mul(t,mats[i][vals[v]])
        out=add(out,t)
    assert table(0,len(word))[()]==out
for case in range(550):
    r=rng.randrange(1,7)
    word=list(range(r))+[rng.randrange(r) for _ in range(rng.randrange(12))]
    rng.shuffle(word)
    test(word,[[tuple(rng.randrange(-3,4) for _ in range(4)) for b in (0,1)] for v in word])
print("550 arbitrary-multiplicity signed products match explicit selector summation")
