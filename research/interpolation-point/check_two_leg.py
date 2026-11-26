"""Independent enumeration of two-hub signatures and defect projections."""
from itertools import product,combinations
from math import prod
from random import Random
def pairs(d): return [()]+[(i,) for i in range(d)]+list(combinations(range(d),2))
def rank_factor(f,d):
    p=[[0]*(d+1) for _ in range(d+1)]
    for i in range(1,d+1):
        p[0][i]=p[i][0]=f.get((i-1,),0)%2
        for j in range(1,i):
            p[i][j]=p[j][i]=f.get((j-1,i-1),0)%2
    uv=next(((i,j) for i,j in combinations(range(d+1),2) if p[i][j]),None)
    if uv is None:return [0]*(d+1),[0]*(d+1)
    i,j=uv;a,b=p[i],p[j]
    if not all((a[k]*b[l]+a[l]*b[k])%2==p[k][l] for k,l in combinations(range(d+1),2)):return None
    return a,b
def hubs(a,b,constant):
    d=len(a)-1;out={S:0 for S in pairs(d)}
    for i,j in product(range(d+1),repeat=2):
        if i and j and i==j:continue
        key=tuple(sorted(v-1 for v in (i,j) if v))
        out[key]+=a[i]*b[j]
    out[()]+=constant-a[0]*b[0]
    return out
def value(fs,edges,ws):
    ports=[[t for t,e in enumerate(edges) if i in e] for i in range(len(fs))]
    ans=0
    for ss in product(*(list(f) for f in fs)):
        active=[set(ports[i][j] for j in s) for i,s in enumerate(ss)]
        a=prod(f[s] for f,s in zip(fs,ss))
        ans+=a*prod(ws[e][2*int(e in active[u])+int(e in active[v])] for e,(u,v) in enumerate(edges))
    return ans
def expanded(fs,edges,ws,k):
    gs=[]
    for i,f in enumerate(fs):
        a,b=rank_factor(f,sum(i in e for e in edges));gs.append(hubs(a,b,f.get((),0)))
    delta=[{S:f.get(S,0)-g[S] for S in g} for g,f in zip(gs,fs)]
    assert all(v%2==0 for g in delta for v in g.values())
    ans=0
    for j in range(min(k-1,len(fs))+1):
        for bad in combinations(range(len(fs)),j):
            ans+=value([delta[i] if i in bad else gs[i] for i in range(len(fs))],edges,ws)
    return ans%2**k
rng=Random(347)
for d in range(1,13):
    for _ in range(10):
        a=[rng.randrange(2) for _ in range(d+1)];b=[rng.randrange(2) for _ in a]
        g=hubs(a,b,rng.randrange(11)); f={S:v+2*rng.randrange(-4,5) for S,v in g.items()}
        u,w=rank_factor(f,d); gg=hubs(u,w,f[()])
        assert all((f[S]-gg[S])%2==0 for S in f)
edges=[(0,1),(1,2),(0,2)]
for i in range(30):
    fs=[]
    for v in range(3):
        a=[rng.randrange(2) for _ in range(3)];b=[rng.randrange(2) for _ in a]
        g=hubs(a,b,rng.randrange(-3,5))
        fs.append({S:w+2*rng.randrange(-2,3) for S,w in g.items()})
    ws=[[rng.randrange(-3,4) for _ in range(4)] for _ in edges]
    k=1+i%4
    assert expanded(fs,edges,ws,k)==value(fs,edges,ws)%2**k
print("120 rank-two reconstructions; 30 defect expansions passed")

# Multiedge replay of the explicit high-precision family and the half-edge scaling.
for vcount in range(30):
    edges=[(0,1)]*5;fs=[]
    for i in (0,1):
        chosen=(0,1) if i==0 else (2,3)
        f={S:2*rng.randrange(-3,4)+int(len(S)==2 and S==chosen) for S in pairs(5)}
        f[(4,)]=1
        fs.append(f)
    w=[[2,1,1,1]]*5
    normalized=[{S:2**(2-len(S))*a for S,a in f.items()} for f in fs]
    nw=[[1,1,1,2]]*5
    direct=value(fs,edges,w);scaled=value(normalized,edges,nw)
    assert direct==2*scaled and scaled%2==1
    assert expanded(normalized,edges,nw,3)==(direct//2)%8

# Exhaust all row input patterns for every signed OR4.
for signs in product(range(2),repeat=4):
    for x in product(range(2),repeat=4):
        false=[int(a==b) for a,b in zip(x,signs)]
        base=[false[0],false[1],1,1]
        changed=[1,1,-false[2],false[3]]
        compute=sum(prod(changed[i] if i in S else base[i] for i in range(4)) for S in ((0,1),(2,3)))
        assert compute==int(not all(false))
for x in product(range(2),repeat=4):
    u=[int(x[0]==0),int(x[1]==0),int(x[2]==1),int(x[3]==1)]
    z=[1-a for a in u]
    v=sum(prod(z[i] if i in S else u[i] for i in range(4)) for S in ((0,1),(2,3)))
    assert v==int(len(set(x))==1)
assert rank_factor({(0,1):1,(2,3):1},4) is None
print("30 valuation-scaled contractions, all 256 OR4 and 16 COPY4 rows passed")

# Parity of independent sets on a programmed bipartite graph, via either endpoint.
for _ in range(30):
    n=2
    clauses=[[(j,rng.randrange(2)) for j in rng.sample(range(n),rng.randrange(1,3))] for _ in range(rng.randrange(1,4))]
    right=[]
    for j in range(n):
        a,b,y=3*j,3*j+1,3*j+2
        right.extend([(1<<a)|(1<<b),(1<<a)|(1<<y),(1<<b)|(1<<y)])
    for cl in clauses:right.append(sum(1<<(3*j+neg) for j,neg in cl))
    sat=sum(all(any(((x>>j)&1)^neg for j,neg in cl) for cl in clauses) for x in range(1<<n))
    iscount=sum(1<<sum((S&m)==0 for m in right) for S in range(1<<(3*n)))
    assert (sat-iscount)%2==0
print("30 bipartite NAND parity reductions passed")
