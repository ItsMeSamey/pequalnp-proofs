from functools import lru_cache
from itertools import product

def theta(level):
    if not level:return 2
    return theta(level-1)<<(1<<level)

@lru_cache(maxsize=100000)
def mul(level,a,b):
    if a<2:return a*b
    if b<2:return b*a
    if level==0:
        return 3 if a==b==2 else 2 if a==b==3 else 1
    width=1<<level
    m=(1<<width)-1
    a0,a1=a&m,a>>width
    b0,b1=b&m,b>>width
    lo=mul(level-1,a0,b0)
    hi=mul(level-1,a1,b1)
    return (lo^mul(level-1,theta(level-1),hi))|((mul(level-1,a0^a1,b0^b1)^lo)<<width)

def power(l,x,n):
    v=1
    while n:
        if n&1:v=mul(l,v,x)
        x=mul(l,x,x)
        n//=2
    return v

def eliminate(l,mat,inv=False):
    if not mat:return [] if inv else True
    n=len(mat)
    a=[r[:] + ([int(i==j)for j in range(n)] if inv else [])for i,r in enumerate(mat)]
    for k in range(n):
        i=next((j for j in range(k,n)if a[j][k]),None)
        if i is None:return None if inv else False
        a[i],a[k]=a[k],a[i]
        q=power(l,a[k][k],(1<<(2<<l))-2)
        a[k]=[mul(l,v,q)for v in a[k]]
        for i in range(n):
            if i!=k and a[i][k]:
                h=a[i][k]
                a[i]=[v^mul(l,h,w)for v,w in zip(a[i],a[k])]
    return [r[n:]for r in a] if inv else True

def xor(vals):
    ans=0
    for v in vals:ans^=v
    return ans

def check(n,edges):
    m=len(edges);l=(m-1).bit_length()
    p=[[power(l,1<<(2*j),4**i)for j in range(m)]for i in range(n)]
    good={}
    for c in product(range(1,4),repeat=n):
        if c[0]!=1 or any(c[u]==c[v]for u,v in edges):continue
        w=tuple(int(mul(0,2,c[u])!=c[v])for u,v in edges)
        good[w]=c
    z=next(w for w in product((0,1),repeat=m)if w not in good)
    base=[[xor([p[i][e] for e,(u,v) in enumerate(edges) if v==j]+
               [mul(l,p[i][e],2+z[e])for e,(u,v) in enumerate(edges)if u==j])
           for j in range(n)]for i in range(n)]
    inv=eliminate(l,base,True)
    assert inv is not None
    u=[[xor(mul(l,inv[i][k],p[k][j])for k in range(n))for j in range(m)]for i in range(n)]
    b=[[int(i==j)^u[tail][j] for j in range(m)]for i,(tail,_) in enumerate(edges)]
    for x in product((0,1),repeat=m):
        idx=[i for i,v in enumerate(x)if v]
        minor=[[b[i][j]for j in idx]for i in idx]
        assert (not eliminate(l,minor))==(tuple(a^c for a,c in zip(z,x))in good)
    print(n,m,'field degree over F4',1<<l,'singular principal supports',len(good))

if __name__=='__main__':
    check(3,[(0,1),(1,2),(2,0)])
    check(4,[(i,j)for i in range(4)for j in range(i)])
    check(4,[(0,1),(1,2),(2,3),(3,0),(0,2)])
