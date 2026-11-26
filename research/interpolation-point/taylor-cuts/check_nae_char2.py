"""Compare the two-layer Pfaffian expansion with binary-cycle enumeration in GF(256)."""
import itertools
import random

def mul(a,b):
    v=0
    while b:
        if b&1: v ^= a
        b >>= 1
        a <<= 1
        if a&256: a ^= 0x11b
    return v

def power(a,k):
    v=1
    while k:
        if k&1: v=mul(v,a)
        a=mul(a,a)
        k//=2
    return v

def pf(matrix):
    v=1
    for j in range(0,len(matrix),2):
        pivot=next((i for i in range(j+1,len(matrix)) if matrix[j][i]),None)
        if pivot is None:return 0
        m=j+1
        matrix[pivot],matrix[m]=matrix[m],matrix[pivot]
        for row in matrix:row[pivot],row[m]=row[m],row[pivot]
        p=matrix[j][m]
        v=mul(v,p)
        inv=power(p,254)
        for a in range(j+2,len(matrix)):
            for b in range(a+1,len(matrix)):
                matrix[a][b]^=mul(inv,mul(matrix[j][a],matrix[m][b])^mul(matrix[j][b],matrix[m][a]))
                matrix[b][a]=matrix[a][b]
    return v

def parity_sum(edges, n, pins):
    inc=[[] for _ in range(n)]; demand=[0]*n; arcs=[]; terminals=0; scale=1
    for (a,b,w),pin in zip(edges,pins):
        if pin is not None:
            if pin:
                scale=mul(scale,w); demand[a]^=1; demand[b]^=1
            continue
        inc[a].append(terminals);inc[b].append(terminals+1)
        arcs.append((terminals,terminals+1,w)); terminals+=2
    for verts,t in zip(inc,demand):
        if (len(verts)-t)%2:
            verts.append(terminals);terminals+=1
        arcs.extend((a,b,1) for a,b in itertools.combinations(verts,2))
    if terminals%2:return 0
    matrix=[[0]*terminals for _ in range(terminals)]
    for a,b,w in arcs:matrix[a][b]=matrix[b][a]=w
    return mul(scale,pf(matrix))

def run(rng,clauses,n):
    m=len(clauses); sites=[(x,n+i,s) for i,c in enumerate(clauses) for x,s in c]
    E=len(sites); g=n+m; weights=[[rng.randrange(256) for _ in sites] for _ in range(2)]
    # options are (zero-gate, pinned-edge-layer, pinned-edge-index)
    def opts(layer):
        out=[(-1,-1,-1)]*(m%2)
        out.extend((i,-1,-1) for i in range(m))
        for i,(_,_,s) in enumerate(sites):
            if s:
                out.extend([(-1,j,i) for j in ((0,1) if layer==2 else (layer,))])
        return out
    result=0
    for fo in itertools.product(*(opts(i) for i in range(3))):
        forced=[[None]*E for _ in range(2)];glue=fo[2][0]
        valid=True
        for k,(zero,layer,j) in enumerate(fo):
            if layer>=0:
                if forced[layer][j]==0:valid=False
                forced[layer][j]=1
            elif zero>=0 and k<2:
                for i,(_,v,_) in enumerate(sites):
                    if v==n+zero:
                        if forced[k][i]==1:valid=False
                        forced[k][i]=0
        if not valid:continue
        edges=[];pins=[]
        for i,(a,b,s) in enumerate(sites):
            if glue>=0 and b==n+glue:
                p,q=forced[0][i],forced[1][i]
                if p is not None and q is not None and p!=q:valid=False;break
                edges.append((a,a+g,mul(weights[0][i],weights[1][i])))
                pins.append(p if p is not None else q)
            else:
                for j in (0,1):
                    edges.append((a+j*g,b+j*g,weights[j][i]));pins.append(forced[j][i])
        if valid:result ^= parity_sum(edges,2*g,pins)
    cycles=[]; negatives=set()
    for mask in range(1<<E):
        syndrome=0; touched=set();sign=0
        for i,(a,b,s) in enumerate(sites):
            if mask>>i&1:
                syndrome ^= (1<<a)|(1<<b);touched.add(b);sign^=s
        if not syndrome:
            cycles.append(mask)
            if (len(touched)+sign)%2: negatives.add(mask)
    direct=0
    for x,y in itertools.product(negatives,repeat=2):
        if x^y in negatives:
            v=1
            for j,mask in enumerate((x,y)):
                for i,w in enumerate(weights[j]):
                    if mask>>i&1:v=mul(v,w)
            direct^=v
    assert direct==result,(clauses,direct,result)
    return (result!=0)
rng=random.Random(3799)
nonzero=0
for i in range(30):
    n=rng.randrange(2,5)
    clauses=[[(x,rng.randrange(2)) for x in rng.sample(range(n),rng.randint(2,n))]
             for j in range(rng.randint(1,3))]
    nonzero+=run(rng,clauses,n)
print('30 two-layer evaluations verified;',nonzero,'nonzero')
