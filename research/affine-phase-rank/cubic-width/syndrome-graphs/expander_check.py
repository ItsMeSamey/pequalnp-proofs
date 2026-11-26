from itertools import product
from math import comb

def recover(n,e,k,value):
    digits=[]
    base=1<<k
    for _ in range(e+1):
        c=(value+base//2)%base-base//2
        digits.append(c)
        value=(value-c)//base
    assert value==0
    raw=sum(c*sum((-1)**j*comb(d,j)*comb(e-d,n//2-j) for j in range(max(0,n//2-e+d),min(d,n//2)+1)) for d,c in enumerate(reversed(digits)))
    assert raw%(1<<n)==0
    return raw//(1<<n)

N=8
edges=[(i,i+4) for i in range(4)]
for v in range(2):
    for i in range(4):
        edges.extend([(4*v+i,N),(4*v+(i+1)%4,N)])
        N+=1
    edges.append((4*v,N))
    N+=1
counts=[1]+[0]*((1<<N)-1)
for u,v in edges:
    flip=(1<<u)|(1<<v)
    counts=[3*x+counts[i^flip] for i,x in enumerate(counts)]
scale=12**8*4*16
assert (counts[-1]<<N)%scale==0
assert recover(2,1,4,(counts[-1]<<N)//scale)==1
print('Full 18-vertex all-odd count:',counts[-1])
for n in [2,4]:
    pairs=[(i,j) for i in range(n) for j in range(i)]
    for mask in range(1<<len(pairs)):
        es=[p for i,p in enumerate(pairs) if mask>>i&1]
        m=len(es)
        k=n+2
        val=sum((-1)**sum(s)*(1<<(k*(m-sum(s[i]!=s[j] for i,j in es)))) for s in product(range(2),repeat=n))
        pm=sum(all(sum(v in p for i,p in enumerate(es) if u>>i&1)==1 for v in range(n)) for u in range(1<<m))
        assert recover(n,m,k,val)==pm
print('66 signed-radix polynomial fixtures passed')
