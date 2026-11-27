"""Independent whole-row rank check with coupled outside hyperedges and joint radius."""
from itertools import combinations,product
from random import Random

def rank(rows,p):
    piv={}
    for x in rows:
        v=list(x)
        for j in sorted(piv):
            c=v[j]
            if c:v=[(a-c*b)%p for a,b in zip(v,piv[j])]
        j=next((i for i,a in enumerate(v) if a),None)
        if j is not None:
            piv[j]=[a*pow(v[j],-1,p)%p for a in v]
    return len(piv)

def verify(quota,N,O,F,d,p):
    items=set.union(*(N+O))
    mon=[set(s) for i in range(d+1) for s in combinations(items,i)]
    full=[];sample=[]
    outside=set.union(*O)
    for h in range(len(outside)+1):
        for raw in combinations(outside,h):
            T=set(raw)
            if any(e<=T for e in F):continue
            k=[q-len(T&o) for q,o in zip(quota,O)]
            if min(k)<0:continue
            free=[{v for v in R if not any(e<=T|{v} for e in F)} for R in N]
            if h<=d and any(len(R)-q<min(d-h,q) for R,q in zip(free,k)):
                return None
            choices=[list(map(set,combinations(sorted(R),q))) for R,q in zip(free,k)]
            for B in product(*choices):
                X=T.union(*B)
                assert not any(e<=X for e in F)
                row=tuple(int(s<=X) for s in mon)
                full.append(row)
                if h<=d and sum(len(Bi-ci[0]) for Bi,ci in zip(B,choices))<=d-h:
                    sample.append(row)
    assert rank(full,p)==rank(sample,p)
    return True

if __name__=="__main__":
    rng=Random(43112)
    passed=0
    for it in range(75):
        q=rng.choice([(1,1),(1,2),(0,1),(2,1),(1,1,1)])
        d=rng.choice([1,2])
        n=0;N=[];O=[]
        for k in q:
            size=k+min(d,k)+rng.randrange(2)
            N.append(set(range(n,n+size)));n+=size
            O.append(set(range(n,n+1+rng.randrange(2))));n+=len(O[-1])
        out=set.union(*O)
        allN=set.union(*N)
        F=[]
        for _ in range(4):
            o=set(rng.sample(sorted(out),rng.choice([1,2])))
            if allN and rng.randrange(4):o.add(rng.choice(sorted(allN)))
            F.append(o)
        for p in [2,3,5]:
            if verify(q,N,O,F,d,p):passed+=1
    assert passed>50
    print(passed,"valid graph/field product-slice comparisons passed")
