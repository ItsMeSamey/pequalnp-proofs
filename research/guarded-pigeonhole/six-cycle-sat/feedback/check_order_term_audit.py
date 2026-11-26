"""Independent algebraic and physical-order audit of the dummy spoke border."""
from random import Random
from itertools import product
R=Random(60848)
def rank(rows):
    piv={}
    for x in rows:
        while x and x.bit_length() in piv:x^=piv[x.bit_length()]
        if x:piv[x.bit_length()]=x
    return len(piv)
def get(h,i,j):return h[i]>>j&1
def physical(k,i,j):
    # Every mark has its own cut, including those on the same underlying wire.
    # Original cycles may visit the other cuts in either order.
    stars=list(range(k+2)); ends=[s+k+2 for s in stars]
    groups=[[] for _ in range(k)]
    for s,cls in enumerate([i,j,*range(k)]):groups[cls].append(ends[s])
    nxt={}
    for g in [stars,*groups]:
        if g is not stars:R.shuffle(g)
        for l,r in zip(g,g[1:]+g[:1]):nxt[l]=r
    for l,r in zip(stars,ends):nxt[l],nxt[r]=nxt[r],nxt[l]
    v=0;seen=set()
    while v not in seen:seen.add(v);v=nxt[v]
    return int(len(seen)==2*(k+2))
def one(k,i,j):
    base=physical(k,i,j)
    if i!=j:assert base==int(i<j)
    n=k+2
    U=[1<<u for u in (i,j,*range(k))]
    # Add an arbitrary nonsingular even summand to the base alternating form.
    d=2*R.randrange(4);N=k+d
    B=[R.randrange(1<<d)<<k|u for u in U]
    A=[0]*k+[1<<(k+(z^1)) for z in range(d)]
    H=[0]*n;F=[0]*n
    for s in range(n):
        for t in range(s):
            if R.getrandbits(1):F[s]|=1<<t;F[t]|=1<<s
            if R.getrandbits(1):H[s]|=1<<t;H[t]|=1<<s
    def val(h):
        top=[a|(sum((b>>z&1)<<s for s,b in enumerate(B))<<N) for z,a in enumerate(A)]
        return int(rank(top+[b|(w<<N) for b,w in zip(B,h)])==N+n)
    change=get(H,0,1)^get(H,0,2+j)^get(H,2+i,1)^get(H,2+i,2+j)
    assert val(F)^val([a^b for a,b in zip(F,H)])==change
    toggle=[0]*n
    for s in range(k):
        toggle[1]|=1<<(2+s);toggle[2+s]|=2
        for t in range(k):
            if s!=t:toggle[2+s]|=1<<(2+t)
    assert val(F)^val([a^b for a,b in zip(F,toggle)])==int(i==j)
n=0
for k in range(1,8):
    for i,j in product(range(k),repeat=2):
        for t in range(20):one(k,i,j);n+=1
print(n,'physical-order, Pfaffian perturbation and joined-toggle checks passed')
