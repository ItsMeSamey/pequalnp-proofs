"""Finite L=2 native OR/COPY packet contraction with recursive group budget convolution."""
from itertools import product
from fractions import Fraction
from math import prod


def kernel(t,zeta,p,delta):
    q=Fraction(prod(t+4*zeta-a for a in range(-2,2) if a!=delta),2)
    # C'(0)=(0+2)(0+1)(0-1)=-2.
    q=-q
    assert q.denominator%2
    return q.numerator*pow(q.denominator,-1,1<<p)%(1<<p)


def verify(edges,t,zeta,p,signs):
    mod=1<<p
    groups=sorted(set(g for e in edges for g in e))
    ports=[(k,s) for k in range(len(edges)) for s in (0,1)]
    rg=[edges[k][s] for k,s in ports]
    cg=[edges[k][1-s] for k,s in ports]
    # Mode j is sourced at column j and targets row j; all b>0 vanish (tile j-coordinate zero).
    W=[kernel(t,zeta,p,d) for d in (-1,0,1)]
    def ell(y,v):
        return v if y else 1-v
    def oracle(g,Y):
        return any(bit^((signs>>j)&1) for j,bit in Y.items())
    def copy(X):
        return len(set(X.values()))<=1
    children={}
    for g in groups:
        rr=[j for j,h in enumerate(rg) if h==g]
        cc=[j for j,h in enumerate(cg) if h==g]
        incident=sorted(rr+cc)
        for b in product((0,1),repeat=len(incident)):
            mask=sum(v<<j for j,v in zip(incident,b))
            subtotal=0
            for y in product((0,1),repeat=len(rr)):
                Y=dict(zip(rr,y))
                if not oracle(g,Y): continue
                for x in product((0,1),repeat=len(cc)):
                    X=dict(zip(cc,x))
                    if not copy(X): continue
                    term=prod(X[j] for j in cc if mask>>j&1)
                    for j in rr:
                        local=W[2 if j%2==0 else 0]*X[j^1]
                        term*=((2*Y[j]-1)*W[1] if mask>>j&1 else ell(Y[j],local))
                    subtotal+=term
            children[g,mask]=subtotal%mod
    incident={g:sum(1<<j for j in range(len(ports)) if g in (rg[j],cg[j])) for g in groups}
    flat=[0]*p
    for b in range(1<<len(ports)):
        k=b.bit_count()
        if k<p:
            flat[k]=(flat[k]+prod(children[g,b&incident[g]] for g in groups))%mod

    def rec(S,fixed,left):
        if len(S)==1:
            g=S[0]
            return [children[g,fixed&incident[g]]]+[0]*left
        A=S[:len(S)//2]
        B=S[len(S)//2:]
        crossing=[j for j,(u,v) in enumerate(zip(rg,cg)) if (u in A and v in B) or (v in A and u in B)]
        ans=[0]*(left+1)
        for vals in product((0,1),repeat=len(crossing)):
            w=sum(vals)
            if w>left: continue
            b=fixed|sum(v<<j for j,v in zip(crossing,vals))
            av=rec(A,b,left-w)
            bv=rec(B,b,left-w)
            for i,va in enumerate(av):
                for j,vb in enumerate(bv[:left-w-i+1]):
                    ans[w+i+j]=(ans[w+i+j]+va*vb)%mod
        return ans
    assert rec(groups,0,p-1)==flat
    # Direct deformed parent: enumerate one copy value per group, then sum its
    # row bits against native OR, subtracting the unique failing row assignment.
    direct=0
    for x in product((0,1),repeat=len(groups)):
        X=dict(zip(groups,x))
        term=1
        for g in groups:
            failing=1
            for j,h in enumerate(rg):
                if h==g:
                    a=W[1]*X[cg[j]]+W[2 if j%2==0 else 0]*X[cg[j^1]]
                    failing*=ell((signs>>j)&1,a)
            term*=1-failing
        direct+=term
    assert sum(flat)%mod==direct%mod


if __name__=='__main__':
    cases=0
    for edges in [[(0,1),(1,2),(2,3)],[(0,1),(1,2),(2,3),(3,0)],[(0,1),(0,2),(0,3)]]:
        for t,z,p,s in product((-1,1),(-1,1,2),(2,4,6),(0,37)):
            verify(edges,t,z,p,s)
            cases+=1
    print(cases,'physical four-group OR/COPY spectra matched flat vs bisection and direct scalar parent')
