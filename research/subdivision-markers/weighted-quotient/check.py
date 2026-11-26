from itertools import combinations
from random import Random

def bit(x): return x.bit_count()&1
def qtimes(Q,c): return sum(bit(row&c)<<i for i,row in enumerate(Q))
def pair_options(Q,c,d):
    target=(c & qtimes(Q,d)) ^ (d & qtimes(Q,c))
    return [(x,y) for x in (0,1) for y in (0,1) if (c*x ^ d*y)==target]

def structural(Q,c):
    inside=[i for i in range(len(Q)) if c>>i&1]
    if len(inside)==1:return 0
    if any(len({Q[i]>>j&1 for i in inside})>1 for j in range(len(Q)) if j not in inside):
        return None
    vals={Q[i]>>j&1 for i in inside for j in inside if i!=j}
    return next(iter(vals)) if len(vals)==1 else None

def local(Q,c):
    return not(c & qtimes(Q,c)) and all(pair_options(Q,c,1<<j) for j in range(len(Q)))

def pair_predict(c,d,kc,kd):
    return bool(not(c&d) or not(c&~d) or not(d&~c) or kc==kd)

def project(x,labels):
    v=0
    for i,c in enumerate(labels):
        if x>>i&1:v^=c
    return v

def concrete():
    Q=[56]*3+[1,2,4]
    ls=[1<<i for i in range(6)]+[7]
    A=[0]*len(ls)
    for u,v in combinations(range(len(ls)),2):
        [(a,b)]=pair_options(Q,ls[u],ls[v])
        A[u]|=a<<v;A[v]|=b<<u
    for x in range(1<<7):
        y=project(x,ls)
        assert project(x&(x^qtimes(A,x)),ls)==(y&(y^qtimes(Q,y)))
    # Every two-vertex merged block fails after every row switch.
    for u,v in combinations(range(7),2):
        good=False
        for flips in range(128):
            signed=[row^(((1<<7)-1)^(1<<i)) if flips>>i&1 else row
                    for i,row in enumerate(A)]
            outside=127^((1<<u)|(1<<v))
            same_out=(signed[u]^signed[v])&outside==0
            same_in=all(((signed[w]>>u)^(signed[w]>>v))&1==0
                        for w in range(7) if outside>>w&1)
            even_internal=((signed[u]>>v)^(signed[v]>>u))&1==0
            good |= same_out and same_in and even_internal
        assert not good

def main():
    rng=Random(813)
    examples=tests=pairtests=0
    for n in (3,4,5,6,7):
        for it in range(1000):
            if it<3:
                Q=[0 if it==0 else (1<<n)-1-(1<<i) for i in range(n)]
            else:
                Q=[rng.randrange(1<<n)&~(1<<i) for i in range(n)]
            eligible=[]
            for c in range(1,1<<n):
                if not bit(c):continue
                k=structural(Q,c)
                assert (k is not None)==local(Q,c)
                eligible.append((c,k)) if k is not None else None
                tests+=1
            for (c,kc),(d,kd) in combinations(eligible,2):
                assert bool(pair_options(Q,c,d))==pair_predict(c,d,kc,kd)
                pairtests+=1
            examples+=1
    concrete()
    print(examples,'base graphs;',tests,'odd supports;',pairtests,'eligible support pairs')
if __name__=='__main__': main()
