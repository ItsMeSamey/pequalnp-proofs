from random import Random
from external import external_table
r=Random(2092)
for test in range(1200):
 n=r.randrange(1,11); h=r.randrange(1,5)
 J=[0]*n; labels=[r.randrange(1<<h) for _ in range(n)]
 for i in range(n):
  for j in range(i):
   if r.randrange(3)==0:J[i]|=1<<j;J[j]|=1<<i
 nodes=list(range(n));r.shuffle(nodes)
 while len(nodes)>1:
  a=nodes.pop(r.randrange(len(nodes))); b=nodes.pop(r.randrange(len(nodes))); nodes.append((a,b))
 forced=r.randrange(1<<n); p=r.randrange(1<<h)
 found=external_table(J,labels,forced,p,nodes[0]); valid={}
 for z in range(1<<n):
  if z&forced!=forced or any(z>>i&1 and ((J[i]&z).bit_count()+(labels[i]&p).bit_count())%2 for i in range(n)):continue
  g=0
  for i,x in enumerate(labels):
   if z>>i&1:g^=x
  valid[z]=g
 assert set(found)==set(valid.values()) and all(valid[z]==g for g,z in found.items())
print('1200 external decomposition tables and witnesses match full enumeration')
