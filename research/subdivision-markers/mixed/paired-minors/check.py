from itertools import combinations
from random import Random

def echelon(cols):
    piv={}
    for x in cols:
        while x and x.bit_length() in piv:
            x ^= piv[x.bit_length()]
        if x:
            piv[x.bit_length()]=x
    return piv

def rank(cols):
    return len(echelon(cols))

def quotient(x,piv):
    for k in sorted(piv,reverse=True):
        if x>>(k-1)&1:
            x^=piv[k]
    return x

def common_basis(a,b,r):
    chosen=set()
    ground=set(range(len(a)))
    def indep(mat,S):
        return rank(mat[i] for i in S)==len(S)
    while len(chosen)<r:
        outside=ground-chosen
        path={j:None for j in outside if indep(a,chosen|{j})}
        queue=list(path)
        for j in queue:
            if j in chosen:
                nexts=[k for k in outside if indep(a,chosen-{j}|{k})]
            else:
                if indep(b,chosen|{j}):
                    while j is not None:
                        chosen.symmetric_difference_update({j})
                        j=path[j]
                    break
                nexts=[k for k in chosen if indep(b,chosen-{k}|{j})]
            for k in nexts:
                if k not in path:
                    path[k]=j
                    queue.append(k)
        else:
            return None
    return sorted(chosen)

def parity(a,x):
    return (a&x).bit_count()%2

def tester(a,L,ends,r,alpha,beta,k0,k1):
    enc=lambda x:parity(alpha,x)|(parity(beta,x)<<1)
    dim=max(a+[v for v,g in ends]+[0]).bit_length()
    aux=echelon([v|((k^enc(g))<<dim) for (v,g),k in zip(ends,(k0,k1))])
    if len(aux)!=2:
        return None
    b=[quotient(x|(enc(g)<<dim),aux) for x,g in zip(a,L)]
    return common_basis(a,b,r)

def tableau(a,L,ends,B):
    rep={0:0}
    for j in B:
        rep.update({x^a[j]:g^L[j] for x,g in list(rep.items())})
    return tuple(g^rep[v] for v,g in ends)

def predicate(pair,A,B,k,l):
    u,v=pair
    a=(k&1)^parity(A,u)
    b=(l&1)^parity(A,v)
    c=(k>>1)^parity(B,u)
    d=(l>>1)^parity(B,v)
    return (a*d)^(b*c)

if __name__=='__main__':
    rng=Random(8441)
    a=[1,2,3,4,8,12,16]
    L=[4,0,0,8,0,0,0]
    ends=[(17,1),(20,2)]
    b=tester(a,L,ends,5,4,8,1,2)
    assert tableau(a,L,ends,b)==(1,2)
    print('connected example private basis',b,'residuals',(1,2))
    num=0
    for trial in range(160):
        r=rng.randint(2,5)
        a=[1<<i for i in range(r)]+[rng.randrange(1<<r) for j in range(rng.randint(1,5))]
        L=[rng.randrange(16) for _ in a]
        ends=[(rng.randrange(1<<r),rng.randrange(16)) for j in range(2)]
        bases=[S for S in combinations(range(len(a)),r) if rank(a[i] for i in S)==r]
        states={tableau(a,L,ends,S) for S in bases}
        for _ in range(32):
            args=(rng.randrange(16),rng.randrange(16),rng.randrange(4),rng.randrange(4))
            b=tester(a,L,ends,r,*args)
            assert (b is not None)==any(predicate(p,*args) for p in states)
            if b is not None:
                assert predicate(tableau(a,L,ends,b),*args)
            num+=1
    print(num,'represented common-basis tests verified against all private bases')
