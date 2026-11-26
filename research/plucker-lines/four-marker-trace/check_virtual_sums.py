from itertools import product
from random import Random

def models(cols,alpha,beta,r):
    ok=[]
    for c in range(1<<len(cols)):
        val=out=0
        for j,e in enumerate(cols):
            if c>>j&1:val^=e;out^=alpha[j]
        if val:continue
        for d in range(1<<r):
            mask=sum(((d&e).bit_count()%2)<<j for j,e in enumerate(cols))
            if mask&c:continue
            z=out
            for j in range(len(cols)):
                if mask>>j&1:z^=beta[j]
            ok.append((c,mask,z))
    return ok

def run(R,k):
    # Two distinct torso ports 1 and 2; every port has ordinary substitutes.
    C=[1,2,3,R.randrange(1,4),1,2]
    t=4; A=[R.randrange(1<<k) for _ in range(4)]+[0,0]
    B=[R.randrange(1<<k) for _ in range(4)]+[0,0]
    core=models(C,A,B,2); globalcols=C[:4]; aa=A[:4]; bb=B[:4]
    tables=[]
    for j in range(2):
        local=[2,3,R.randrange(1,4),1]
        a=[R.randrange(1<<k) for _ in range(3)]+[0];b=[R.randrange(1<<k) for _ in range(3)]+[0]
        scores={m:set() for m in [0,1,2]}
        for c,d,z in models(local,a,b,2):
            m=(c>>3&1)+2*(d>>3&1)
            scores[m].add(z)
        assert all(scores.values())
        tables.append(scores)
        for e in local[:3]:globalcols.append(((e&1)<<j)^((e>>1)<<(j+2)))
        aa+=a[:3];bb+=b[:3]
    direct={s for c,d,s in models(globalcols,aa,bb,4)}
    shifted=set()
    for c,d,base in core:
        vals=[tables[j][(c>>(t+j)&1)+2*(d>>(t+j)&1)] for j in range(2)]
        first=[min(s) for s in vals]
        for x,y in product(*vals):
            if (x!=first[0])+(y!=first[1])<=k:shifted.add(base^x^y)
    assert direct==shifted
if __name__=='__main__':
    rng=Random(6156)
    for k in [1,2,3,4]:
        for _ in range(40):run(rng,k)
    print('160 two-limb represented sums passed over score ranks 1–4')
