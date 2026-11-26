"""Verify balanced flag deletions, pair kernel and q401 certificate numerics."""
from itertools import combinations
from fractions import Fraction as F
from math import comb

for q,h in [(2,1),(3,1),(3,2)]:
    rows=[(1,i,j) for i in range(q) for j in range(q)]+[(0,1,i) for i in range(q)]+[(0,0,1)]
    N=len(rows)
    inc=[{i for i,v in enumerate(rows) if sum(x*y for x,y in zip(u,v))%q==0} for u in rows]
    count=0; pair=[0]*4
    p=0;l=next(iter(inc[p]));ln=next(i for i in range(N) if i not in inc[p])
    for o in range(N):
        for g in inc[o]:
            for A0 in combinations(inc[g]-{o},h):
                for B0 in combinations(inc[o]-{g},h):
                    A=set(A0);B=set(B0)
                    ZP=set().union(*(inc[j] for j in B)); ZL=set().union(*(inc[j] for j in A))
                    assert not ZP&A and not ZL&B
                    P=ZP|A;L=ZL|B
                    assert len(P)==len(L)==h*(q+1)+1
                    deg=[len(inc[i]-L) for i in range(N) if i not in P]
                    deg +=[len(inc[i]-P) for i in range(N) if i not in L]
                    assert min(deg)==q+1-h
                    pair[0]+=p in P
                    pair[1]+=int(0 in P and 1 in P)
                    pair[2]+=int(p in P and l in L)
                    pair[3]+=int(p in P and ln in L)
                    count+=1
    d=h*(q+1)+1
    e=1+2*h*(q+1)+h*h*q
    assert [F(k,count) for k in pair]==[F(d,N),F(d*(d-1),N*(N-1)),F(e,N*(q+1)),F(d*d-e,N*(N-q-1))]
    print(q,h,count)
q=401;N=q*q+q+1
for h in (25,33):
    d=h*(q+1)+1;e=1+2*h*(q+1)+h*h*q
    n=2*(N-d);k=q+1-h
    req=(q*N+99)//100-(2*n-1-(2*n)//(k+1))
    p=F(d,N);J=max(F(d*(d-1),N*(N-1)),F(e,N*(q+1)),F(d*d-e,N*(N-q-1)))
    if h==25: assert req==43417
    else: assert req==56281 and (p-J/2)*4*N+(3*p/2-3*J)*54091>=req
    print(q,h,req)
