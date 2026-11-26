from itertools import combinations
from search_chart_additive import reduce_vec,insert
def det(rows):
    b={}
    return all(insert(x,b) for x in rows)
def minor(cols,rows):
    mask=sum(1<<i for i in rows)
    return int(det([c&mask for c in cols]))
def scan(cols,r,s,t,ell,u):
    n=len(cols);lift=[v|(((ell>>i)&1)<<r) for i,v in enumerate(cols)]
    piv={};narrow={};states=set();grid=[]
    coord=list(combinations(range(r+1),r-1))
    for X in combinations([i for i in range(n) if i not in (s,t)],r-1):
        L=[cols[i] for i in X];Z=[lift[i] for i in X]
        a=int(det(L+[cols[s]]));b=int(det(L+[cols[s]^cols[t]]))
        d=int(det(Z+[lift[s],lift[t]]));e=int(det(L+[u]))
        val=a*b*(d^e);g=d^e;states.add((a,b,g))
        vec=[minor(Z,I) for I in coord]
        def quad(v):
            v=[1]+v
            return sum((v[i]&v[j])<<k for k,(i,j) in enumerate(combinations(range(len(v)),2)))
        # Constant and squares handled separately
        def aug(v):
            return 1|(quad(v)<<1)
        i=len(grid);grid.append((X,a,b,g))
        for p,v in ((piv,vec),(narrow,[a,b,g])):
            row=(aug(v)<<1)|val
            rem=insert(row,p)
    return 0 in piv,0 in narrow,states,grid
if __name__=='__main__':
    C=[13,4,2,5,1,8,14,7,3]
    print(scan(C,4,0,1,64,0)[:3])
def safe_forms(cols,r,s,t):
    n=len(cols);safe={}
    for X in combinations([i for i in range(n) if i not in (s,t)],r-1):
        if not det([cols[i] for i in (*X,s)]) or not det([cols[i] for i in X]+[cols[s]^cols[t]]):continue
        B=(*X,s);co={0:0}
        for i in B:co.update({v^cols[i]:w|(1<<i) for v,w in co.items()})
        c={j:co[v]|1<<j for j,v in enumerate(cols) if j not in B}
        d={i:1<<i|sum(1<<j for j in c if c[j]>>i&1) for i in B}
        for j in c:
            if j!=t and not (c[j]>>s&1):insert(c[j],safe)
        for i in B:
            if i!=s and not (c[t]>>i&1):insert(d[i]<<n,safe)
    ans=[]
    for h in range(2*n):
        if h in safe:continue
        z=1<<h
        for i,row in sorted(safe.items()):
            if (z&row).bit_count()%2:z^=1<<i
        ans.append(z)
    return ans
if __name__=='__main__':
    from random import Random
    rng=Random(4321)
    for _ in range(500):
        r=rng.randint(3,5);n=rng.randint(r+3,min(2**r-1,r+8))
        C=rng.sample(range(1,2**r),n)
        basis=safe_forms(C,r,0,1)
        for z in [__import__('functools').reduce(int.__xor__,[v for v in basis if rng.getrandbits(1)],0) for _ in range(4)]:
            ell=z%2**n;u=__import__('functools').reduce(int.__xor__,[v for i,v in enumerate(C) if z>>(n+i)&1],0)
            broad,narrow,states,grid=scan(C,r,0,1,ell,u)
            if narrow:
                print('narrow-obstruction',r,C,ell,u,states,broad,flush=True);quit()
