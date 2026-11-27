"""Small GF(2) centroid and field-quadratic fiber controls."""
from random import Random
from collections import Counter
from hidden_cubing_polar import nullspace,mul,apply,invertible


def centroid(beta,r):
    n=len(beta)
    width=n*n+r*r
    rows=[]
    for i in range(n):
        for j in range(n):
            eqs=[0]*r
            for k in range(n):
                for h in range(r):
                    if beta[k][j]>>h&1:eqs[h]^=1<<(n*i+k)
            for k in range(r):
                if beta[i][j]>>k&1:
                    for h in range(r):eqs[h]^=1<<(n*n+r*k+h)
            rows.extend(eqs)
    return nullspace(rows,width)


def test(r,pairs,rng):
    mod={2:7,3:11}[r]
    Q=1<<r
    n=2*r*pairs
    C=invertible(n,rng); D=invertible(r,rng)
    def field_trace(x):
        ans=0
        for _ in range(r):
            ans^=x
            x=mul(x,x,mod)
        return ans
    for anis in (0,1):
        c=next(a for a in range(Q) if field_trace(a)==anis)
        def H(x):
            ans=0
            for i in range(pairs):
                a=x>>(2*r*i)&(Q-1)
                b=x>>(2*r*i+r)&(Q-1)
                ans^=mul(a,b,mod)
                if i==0:ans^=mul(a,a,mod)^mul(c,mul(b,b,mod),mod)
            return ans
        beta=[[Dval for Dval in (apply(D,H(C[i]^C[j])^H(C[i])^H(C[j])) for j in range(n))] for i in range(n)]
        basis=centroid(beta,r)
        assert len(basis)==r
        # All field-linear perturbations arise by B(x,t) for the unique t.
        for _ in range(5):
            t=rng.randrange(1<<n)
            offset=rng.randrange(Q)
            hist=Counter(apply(D,H(apply(C,x)^t)^offset) for x in range(1<<n))
            exc=apply(D,offset)
            sign=(-1)**anis
            for y in range(Q):
                assert hist[y]==Q**(2*pairs-1)+sign*Q**(pairs-1)*(Q-1 if y==exc else -1)
        if (r,pairs,anis)==(2,1,1):
            for hole in range(16):
                zeros=[x for x in range(16) if H(apply(C,x^hole))==0]
                assert zeros==[hole]
    print('field size',Q,'field dimension',2*pairs,'binary centroid dimension',len(basis),'both Arf signs passed')


if __name__=='__main__':
    rng=Random(931)
    for r,k in ((2,1),(3,1),(2,2)):test(r,k,rng)
