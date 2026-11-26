from itertools import combinations, product

def f4(x,y):
    z=0
    while y:
        if y&1: z^=x
        y>>=1
        x<<=1
        if x&4: x^=7
    return z

def mul(x,y):
    a,b=x&3,x>>2
    c,d=y&3,y>>2
    bd=f4(b,d)
    return (f4(a,c)^f4(2,bd))|((f4(a,d)^f4(b,c)^bd)<<2)

def div(x,y):
    return next(z for z in range(16) if mul(y,z)==x)

def rankf(columns):
    base={}
    for col in columns:
        v=list(col)
        for i in range(len(v)):
            if not v[i]: continue
            if i not in base:
                denom=v[i]
                base[i]=[div(z,denom) for z in v]
                break
            t=v[i]
            v=[x^mul(t,y) for x,y in zip(v,base[i])]
    return len(base)

def binary(x,r=6):
    return [(x>>i)&1 for i in range(r)]

r=6
q=[1<<i for i in range(r)]+[63,42]
gain=[0]*6+[1,2]
w=[x|(y<<2) for x,y in zip(binary(51),binary(60))]
p0=1|(2<<2)
N=[[a^div(mul(z,g),p0) for a,z in zip(binary(t),w)] for t,g in zip(q,gain)]
sc=[div(1,v) for v in N[6]]
scaled=[[mul(k,z) for k,z in zip(sc,c)] for c in N]
gp=scaled[-1]
slices=[sum(((v>>j)&1)<<i for i,v in enumerate(gp)) for j in range(4)]
wins=[];tot=0
for B in combinations(range(8),r):
    if rankf([binary(q[i]) for i in B])==r:
        tot+=1
        if rankf([N[i] for i in B])<r: wins.append(B)
def dot(h,x): return (h&x).bit_count()%2
roots=[h for h in range(64) if dot(h,q[-1]) and all(not dot(h,s) for s in slices)
       and rankf([binary(x) for x in q[:-1] if not dot(h,x)])==5]
print('w,p0,scaling,gprime,slices,slice rank:',w,p0,sc,gp,slices,rankf(list(map(binary,slices))))
print('sector masks and local ranks (root plus slices):',[(s,sum(1<<i for i,z in enumerate(w) if z==s),rankf([binary(x&sum(1<<i for i,z in enumerate(w) if z==s)) for x in [42]+slices])) for s in set(w)])
print('binary bases, differing bases, normals:',tot,wins,roots)
assert len(wins)==len(roots)>0
for B in wins:
    assert 7 in B
    h=next(h for h in roots if all(not dot(h,q[j]) for j in B if j!=7))
    pairs=[(v,t) for v,t in zip(q,gain) if v in [q[i] for i in B]]
    table={0:0}
    for v,t in pairs:
        table.update({s^v:g^t for s,g in list(table.items())})
    assert (table[51],table[60])==(1,2)
    print('interpolant on unit vectors:',[table[1<<i] for i in range(6)])

# Independently select local traces with physical backpointers, then complete.
def span(columns):
    S={0}
    for v in columns:
        S|={s^v for s in S}
    return frozenset(S)
sectors=[sum(1<<i for i,z in enumerate(w) if z==typ) for typ in (1,4,5)]
K=span([x for sector in sectors for x in (sector,42&sector)])
blocks=[[i for i in range(6) if sector>>i&1] for sector in sectors]+[[6]]
dp={frozenset({0}):()}
for block in blocks:
    local={}
    for m in range(1<<len(block)):
        ids=tuple(i for j,i in enumerate(block) if m>>j&1)
        local[span(q[i] for i in ids)&K]=ids
    dp={span((*x,*y)):ids+more for x,ids in dp.items() for y,more in local.items()}
eligible=[ids for tr,ids in dp.items() if all(s in tr for s in slices) and 42 not in tr]
assert eligible
full={span(q[i] for i in range(7) if m>>i&1)&K for m in range(128)}
assert set(dp)==full
print('DP traces, positive cells, physical selection:',len(dp),len(eligible),eligible[0])
