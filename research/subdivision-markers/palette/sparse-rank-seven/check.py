from collections import Counter
from itertools import combinations
E=[17,23,24,28,35,38,40,47,62,64,74,83,90,92,100,104,109]
def span(a):
 z=1
 for v in a:
  z|=sum(1<<(i^v) for i in range(128) if z>>i&1)
 return z
def plus(s,v):
 return s|sum(1<<(i^v) for i in range(128) if s>>i&1)
def rk(s):return s.bit_count().bit_length()-1
S=[1]
for v in E:S.extend(plus(s,v) for s in S[:])
U=(1<<16)-1
R={s&U for s in S}
H=15
assert len(R)==66 and H not in R
n=len(E);full=(1<<n)-1
aug={s:plus(plus(plus(plus(s,1),2),4),8) for s in set(S)}
j=Counter(rk(s)+rk(aug[S[m^full]])-7 for m,s in enumerate(S) if m.bit_count()>=7)
conn=[min(rk(S[m])+rk(S[m^full])-7 for m in range(full+1) if i<=m.bit_count()<=n-i) for i in range(1,9)]
print('j',j,'conn',conn)
K={}
for f in range(64):
 k=span([(16<<i) | ((f>>(2*i)&3)<<2) for i in range(3)])
 hits=[v for v in E if k>>(v&~3)&1]
 key=len(hits),rk(span(v>>4 for v in hits)),rk(span(hits))
 K[key]=K.get(key,0)+1
print('charts',sorted(K.items()))
print('rank total',rk(S[-1]),'round', all(rk(s)==7 or rk(S[full^m])==7 for m,s in enumerate(S)))
print('min loss of H containment',min(m.bit_count() for m in range(full+1) if S[full^m]&H!=H))
print('min subset conflict',min(m.bit_count() for m,s in enumerate(S) if s&(U^H)))
