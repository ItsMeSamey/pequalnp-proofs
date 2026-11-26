from itertools import combinations
from math import gcd

def fibonacci(k):
    f=[0,1]
    while len(f)<4 or f[-1]%k:
        f.append(f[-1]+f[-2])
    return len(f)-1,f[-2]%k

def gadget(n,edges,k):
    t,b=fibonacci(k)
    parts=[]; rows=[]
    def vertex(side):
        parts.append(side);rows.append(0);return len(rows)-1
    def join(u,v):
        assert parts[u]!=parts[v]
        rows[u]|=1<<v;rows[v]|=1<<u
    def path(root,l):
        for _ in range(l):
            v=vertex(1-parts[root]);join(root,v);root=v
    for i in range(n):vertex(0)
    p=vertex(0);path(p,t-2)
    for i in range(n):
        v=vertex(1);join(v,p);join(v,i)
    for u,v in edges:
        w=vertex(0)
        a=vertex(1);c=vertex(1)
        join(w,a);join(w,c);join(u,a);join(v,c)
        path(w,t-2);path(a,t-3)
    return rows,parts,pow(b,2*len(edges)+1,k)

def brute(rows,parts,k):
    left=[i for i,s in enumerate(parts) if s==0]
    right=[i for i,s in enumerate(parts) if s==1]
    if len(left)>len(right):left,right=right,left
    total=0
    for j in range(1<<len(left)):
        x=sum(1<<v for i,v in enumerate(left) if j>>i&1)
        cols=[rows[r]&x for r in right if (rows[r]&x).bit_count()%2==0]
        piv={}
        for v in cols:
            while v:
                i=v.bit_length()
                if i not in piv:piv[i]=v;break
                v^=piv[i]
        total+=pow(2,len(cols)-len(piv),k)
    return total%k

cases=0
for k in [2,3,4,5,6,7,8,9,10,11,12,13,16,21]:
    t,b=fibonacci(k)
    assert gcd(b,k)==1
    for n in [2,3,4]:
        E=list(combinations(range(n),2))
        for code in range(1<<len(E)):
            edges=[e for i,e in enumerate(E) if code>>i&1]
            rows,parts,factor=gadget(n,edges,k)
            if min(parts.count(0),parts.count(1))>13:continue
            expected=sum(all(not((s>>u)&(s>>v)&1) for u,v in edges) for s in range(1<<n))
            assert brute(rows,parts,k)==factor*expected%k
            cases+=1
print(cases,'full bipartite modular reductions passed.')
