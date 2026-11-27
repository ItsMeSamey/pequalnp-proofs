"""Compare optional-swap spanning forests with marked physical permutation orbits."""
from itertools import product, combinations
from random import Random

def parts(perm):
    d={}
    for i in range(len(perm)):
        v=i
        while v not in d:
            d[v]=i
            v=perm[v]
    return d

def run(count=1500):
    rng=Random(491)
    roots=accepted=0
    for _ in range(count):
        sizes=[rng.choice((2,3)) for _ in range(rng.randrange(1,5))]
        p=rng.sample(range(sum(sizes)),sum(sizes))
        base=parts(p)
        allparts=[];forests=[]
        for mode in product((0,1),repeat=len(sizes)):
            q=p[:];i=0;rank=0;d=base.copy();forest=True
            for n,h in zip(sizes,mode):
                if n==3 or h:
                    j=i+(1+h if n==3 else 1)
                    q[i],q[j]=q[j],q[i]
                    x,y=d[i],d[j]
                    if x==y:forest=False
                    else:d={k:(x if v==y else v) for k,v in d.items()}
                i+=n
            allparts.append(parts(q))
            if forest:forests.append(d)
        if not forests:continue
        accepted+=1
        for r,s in combinations(range(len(p)),2):
            if any(d[r]==d[s] for d in allparts)!=any(d[r]==d[s] for d in forests):
                raise AssertionError((sizes,p,r,s))
            roots+=1
    print(accepted,'eligible references;',roots,'root pairs')
if __name__=='__main__':run()
