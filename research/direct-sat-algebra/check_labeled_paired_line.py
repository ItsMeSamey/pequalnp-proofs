"""Small controls for the optional Pfaffian and nilpotent residue identities."""
from itertools import combinations, product
from random import Random
from functools import lru_cache
from punctured_witness import BinaryField
from label_subset_ring import LabelRing
from additive_slope_prefix import _det

rng=Random(3002)
f=BinaryField(19)

def mul(r,a,b):
    if a==r.zero or b==r.zero: return r.zero
    out=[0]*r.size
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if not i&j and x and y:
                out[i|j]^=f.mul(x,y)
    return tuple(out)

def scale(c,x):
    return tuple(f.mul(c,v) for v in x)

def constant(r,c):
    return scale(c,r.one)

def rs(r,items):
    out=r.zero
    for x in items: out=r.add(out,x)
    return out

def pf(r,rows):
    @lru_cache(None)
    def go(mask):
        if not mask:return r.one
        i=(mask&-mask).bit_length()-1
        return rs(r,(mul(r,rows[i][j],go(mask^(1<<i)^(1<<j))) for j in range(i+1,len(rows)) if mask>>j&1))
    return go((1<<len(rows))-1)

def contraction():
    r=LabelRing(f,3)
    for trial in range(140):
        a=rng.randrange(1,5)
        g=[rng.randrange(4) for _ in range(a)]
        D=[[0]*(2*a) for _ in range(2*a)]
        for i,j in combinations(range(2*a),2):
            D[i][j]=D[j][i]=rng.randrange(f.size)
        mandatory=[]; optional=[]; factors=r.one
        options=[]
        for i,gi in enumerate(g):
            alpha,beta=[rng.randrange(1,f.size) for _ in range(2)]
            B=(0,)+tuple(rng.randrange(f.size) for _ in range(7))
            i0,i1=i,i+a
            u={i0:constant(r,beta),i1:constant(r,alpha)}
            if gi==0:
                mandatory.extend([{i0:r.one},{i1:r.one}])
                options.append([((i0,i1),r.one)])
            elif gi==1:
                mandatory.append(u);optional.append({i1:scale(f.inverse(beta),B)})
                options.append([((i0,),constant(r,beta)),((i1,),constant(r,alpha)),((i0,i1),B)])
            elif gi==2:
                gamma=f.mul(alpha,beta)
                factors=scale(gamma,factors)
                optional.append({k:scale(f.inverse(gamma),mul(r,v,B)) for k,v in u.items()})
                options.append([((),constant(r,gamma)),((i0,),scale(beta,B)),((i1,),scale(alpha,B))])
            else:
                v=scale(f.mul(alpha,beta),B)
                factors=mul(r,factors,v);options.append([((),v)])
        if (len(mandatory)+len(optional))%2: optional.append({})
        cols=mandatory+optional
        mats=[[r.zero]*len(cols) for _ in cols]
        for i,j in combinations(range(len(cols)),2):
            v=rs(r,(scale(f.mul(D[k][l],D[k][l]),mul(r,x,y)) for k,x in cols[i].items() for l,y in cols[j].items()))
            if i>=len(mandatory):v=r.add(v,r.one)
            mats[i][j]=mats[j][i]=v
        got=mul(r,factors,pf(r,mats))
        expected=r.zero
        for opts in product(*options):
            ids=[];weight=r.one
            for idx,w in opts:ids.extend(idx);weight=mul(r,weight,w)
            minor=_det(f,[[D[k][l] for l in ids] for k in ids])
            expected=r.add(expected,scale(minor,weight))
        assert got==expected

def residue():
    # Nonlinear square-zero substitutions over a non-prime field, 2 or 3 pivots.
    for trial in range(120):
        n=5; k=2+trial%2
        full=LabelRing(f,n); small=LabelRing(f,n-k)
        polys=[]
        for j in range(k):
            row=[0]*full.size;row[1<<j]=rng.randrange(1,f.size)
            for mask in range(1,full.size):
                if mask.bit_count()>1 or mask>=1<<k:
                    row[mask]=rng.randrange(f.size)
            polys.append(row)
        V=tuple(rng.randrange(f.size) for _ in range(full.size))
        original=V
        for p in polys:original=mul(full,original,p)
        values=[small.zero]*k+[tuple(int(j==1<<i) for j in range(small.size)) for i in range(n-k)]
        def ev(p,der=None):
            out=small.zero
            for mask,coef in enumerate(p):
                if der is not None:
                    if not mask>>der&1:continue
                    mask^=1<<der
                v=constant(small,coef)
                for j in range(n):
                    if mask>>j&1:v=mul(small,v,values[j])
                out=small.add(out,v)
            return out
        for _ in range(n+1):
            inc=[scale(f.inverse(p[1<<j]),ev(p)) for j,p in enumerate(polys)]
            values[:k]=[small.add(values[j],inc[j]) for j in range(k)]
        assert all(ev(p)==small.zero for p in polys)
        from itertools import permutations
        det=small.zero
        for perm in permutations(range(k)):
            v=small.one
            for j,p in enumerate(polys):v=mul(small,v,ev(p,perm[j]))
            det=small.add(det,v)
        assert mul(small,det,ev(V))[-1]==original[-1]

if __name__=="__main__":
    contraction();residue()
    print("140 optional-block Pfaffians and 120 multivariate residue identities passed")
