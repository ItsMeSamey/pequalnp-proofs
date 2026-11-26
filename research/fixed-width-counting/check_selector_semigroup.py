from itertools import product
from functools import reduce
from random import Random
I=(1,0,0,1)
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def mul(a,b):return tuple(sum(a[2*i+k]*b[2*k+j] for k in (0,1)) for i,j in product((0,1),repeat=2))
def direct(w,M):
    out=(0,0,0,0)
    for x in product((0,1),repeat=max(w)+1):
        out=add(out,reduce(mul,[m[x[v]] for v,m in zip(w,M)],I))
    return out
def cross(w,a,b):
    l=[v for v in w if v in (a,b)]
    return sum(i!=j for i,j in zip(l,l[1:]))>=3
def nc(w,M):
    def rec(i,end,p,b):
        t=I
        while i<end:
            if w[i]==p:
                t=mul(t,M[i][b]);i+=1
            else:
                j=max(j for j in range(i,end) if w[j]==w[i])+1
                t=mul(t,add(rec(i,j,w[i],0),rec(i,j,w[i],1)));i=j
        return t
    return rec(0,len(w),-1,0)
rng=Random(915)
count=0
for trial in range(500):
    r=rng.randrange(1,5)
    w=list(range(r))+[rng.randrange(r) for _ in range(rng.randrange(5))]
    rng.shuffle(w)
    if any(cross(w,a,b) for a in range(r) for b in range(a)):continue
    M=[[tuple(rng.randrange(-2,3) for _ in range(4)) for _ in range(2)] for _ in w]
    assert nc(w,M)==direct(w,M)
    count+=1
adj=[[] for _ in range(6)]
for a in range(3):
    for b in range(3,6):
        for _ in range(1+int(b==a+3)):
            adj[a].append(b);adj[b].append(a)
stack=[0];tour=[]
while stack:
    a=stack[-1]
    if adj[a]:
        b=adj[a].pop();adj[b].remove(a);stack.append(b)
    else:tour.append(stack.pop())
w=tour[::-1][:-1]
assert all(w.count(i)==2 for i in range(6))
M=[(0,0,1,0),(0,1,0,1)]
out=direct(w,[M]*len(w))
assert out[0]+out[3]==15
print(count,"noncrossing signed products and Euler K3,3 checked")
