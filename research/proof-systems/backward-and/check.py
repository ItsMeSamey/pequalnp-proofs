from itertools import combinations
from random import Random
from cofactor import rewrite,value
rng=Random(192)
cases=0;internal=0
for _ in range(250):
    n=rng.randrange(1,7);m=rng.randrange(1,11)
    gates=[(rng.getrandbits(n+j+1),rng.getrandbits(n+j+1)) for j in range(m)]
    out=rng.getrandbits(n+m+1);j=rng.randrange(m);side=rng.randrange(2)
    candidates=[k for k in range(1,n+j+1) if gates[j][side]>>k&1]
    if not candidates:continue
    pivot=rng.choice(candidates)
    reduced,target=rewrite(n,gates,out,j,side,pivot)
    assert all(value(n,gates,out,x)==value(n,reduced,target,x) for x in range(1<<n))
    cases+=1;internal+=pivot>n
for L in range(2,12):
    n=L+1;t=1<<n; gates=[(1<<(i+1),1<<(j+1)) for i,j in combinations(range(L),2)]
    q=sum(1<<(n+1+i) for i in range(len(gates)))
    gates.append((1^t,q))
    parity=sum(1<<(i+1) for i in range(L))
    gates.append((t,(1<<(n+len(gates)))^parity))
    out=1<<(n+len(gates))
    result,target=rewrite(n,gates,out,len(gates)-1,0,n)
    assert len(result)==1
    assert all(value(n,result,target,x)==((x>>L)&(x&((1<<L)-1)).bit_count()&1)
               for x in range(1<<n))
print(cases,'exhaustive raw-input comparisons,',internal,'internal pivots; ten quadratic-size families reduced to one AND')
for L in range(2,12):
    n=L+2;a=1<<(L+1);t=1<<(L+2);s=0;gates=[]
    for i in range(L):
        gates.append((1<<(i+1),a^s))
        s ^= 1<<(n+len(gates))
    gates.append((1^t,s))
    live=a^sum(1<<(i+1) for i in range(L))
    gates.append((t,live^(1<<(n+len(gates)))))
    out=1<<(n+len(gates))
    result,target=rewrite(n,gates,out,len(gates)-1,0,n)
    assert len(gates)==n and len(result)==1
    assert all(value(n,gates,out,x)==value(n,result,target,x) for x in range(1<<n))
print('ten dense m=n controls reduced to one AND')
