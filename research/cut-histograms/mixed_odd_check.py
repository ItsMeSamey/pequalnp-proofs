"""Compile and exhaustively verify small mixed-odd fixed-bin SAT reductions."""
from math import comb
from random import Random

def add(left,right,m):
    out=left.copy()
    for a,c in right.items():
        v=(out.get(a,0)+c)%m
        if v:
            out[a]=v
        else:
            out.pop(a,None)
    return out

def mul(left,right,m):
    out={}
    for a,c in left.items():
        for b,d in right.items():
            k=a^b
            out[k]=(out.get(k,0)+c*d)%m
    return {k:v for k,v in out.items() if v}

def power(a,d,m):
    res={0:1}
    while d:
        if d&1: res=mul(res,a,m)
        a=mul(a,a,m)
        d//=2
    return res

def bit(i,positive,p):
    inv=pow(2,-1,p)
    return {0:inv,1<<i:(-inv if positive else inv)%p}

def compile_code(n,clauses,m):
    factors=[]
    rem=m
    for p in range(2,m+1):
        if rem%p: continue
        q=1
        while rem%p==0:
            q*=p;rem//=p
        factors.append((p,q))
    h=sum(p!=2 for p,q in factors)
    L=len(clauses)
    weights={}
    for p,q in factors:
        if p==2:
            coords={1<<n:1}
        else:
            a=p
            while a**h<=L+1:
                a*=p
            D=a-1
            product=[{0:comb(D,j)%p} if comb(D,j)%p else {} for j in range(D+1)]
            for clause in clauses:
                unsat={0:1}
                for i,positive in clause:
                    unsat=mul(unsat,bit(i,not positive,p),p)
                for j in range(D,0,-1):
                    product[j]=add(product[j],mul(unsat,product[j-1],p),p)
            gated=mul(product[D],bit(n,True,p),p)
            lifted=power(gated,(q//p)*(p-1),q)
            assert sum(lifted.values())%q==0
            coords={key:(-2*v)%q for key,v in lifted.items() if key}
        scale=(m//q)*pow(m//q,-1,q)
        for key,w in coords.items():
            weights[key]=(weights.get(key,0)+scale*w)%m
    cols=[v for v,w in weights.items() for _ in range(w)]
    cols.extend(1<<i for i in range(n+1) for _ in range(m))
    return cols

def run():
    rng=Random(8881)
    for m in (15,21,30,45,105):
        for _ in range(15):
            n=rng.randrange(1,6)
            clauses=[[(i,bool(rng.randrange(2))) for i in rng.sample(range(n),rng.randrange(1,min(n,3)+1))]
                     for _ in range(rng.randrange(0,10))]
            cols=compile_code(n,clauses,m)
            for x in range(1<<(n+1)):
                sat=bool(x>>n) and all(any(bool(x>>i&1)==pol for i,pol in c) for c in clauses)
                got=sum((x&v).bit_count()%2 for v in cols)%m==1
                assert sat==got,(m,n,clauses,x)
    print("75 compiled codes: every message agrees with gated 3SAT at moduli 15,21,30,45,105")
if __name__=="__main__":
    run()
