from random import Random
rng=Random(215)
total=0
for n in range(1,7):
    for _ in range(30):
        word=list(range(n))*2;rng.shuffle(word)
        pos=[[k for k,u in enumerate(word) if u==i] for i in range(n)]
        A=[sum((a<p<b)^(a<q<b) and 1<<j or 0 for j,(p,q) in enumerate(pos)) for a,b in pos]
        d=rng.randrange(1<<n)
        models={x for x in range(1<<n) if all(not(x>>i&1 and (((A[i]&x).bit_count()^(d>>i))&1)) for i in range(n))}
        counts={}
        for e in range(1<<(2*n)):
            x=0
            for i,(a,b) in enumerate(pos):
                i1=e>>((a-1)%(2*n))&1;o1=e>>a&1
                i2=e>>((b-1)%(2*n))&1;o2=e>>b&1
                if d>>i&1:i2,o2=o2,i2
                if i1+i2!=o1+o2:break
                x|=(i1^o1)<<i
            else:counts[x]=counts.get(x,0)+1
        assert set(counts)==models and all(c==2 for c in counts.values())
        total+=1
print('shifted arc/model tables:',total)
