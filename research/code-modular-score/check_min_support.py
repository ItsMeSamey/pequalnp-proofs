from random import Random
r=Random(693)
count=0
for _ in range(500):
    m=r.randrange(1,10)
    joint={0}
    for _ in range(r.randrange(1,7)):
        w=(r.randrange(1<<m)<<3)|r.randrange(8)
        joint|={x^w for x in joint}
    byY=[]
    for Y in range(1<<m):
        words=[x for x in joint if ((x>>3)&~Y)==0]
        byY.append(frozenset(x&7 for x in words))
    ambiguity=byY[0]
    for Y,S in enumerate(byY):
        if any(byY[Y^(1<<i)]==S for i in range(m) if Y>>i&1):continue
        words={x>>3 for x in joint if not (x>>3)&~Y}
        assert len(words)*len(ambiguity)==len(S)
        count+=1
print(count,'minimal physical supports checked with paired row spaces, including ambiguous named lifts')
