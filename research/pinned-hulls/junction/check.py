from itertools import combinations
def pc(n,edges,pins,d):
 ms=[sum(1<<j for j in s) for k in range(d+1) for s in combinations(range(n),k)]
 ix={m:j for j,m in enumerate(ms)}
 low=sum(m.bit_count()<d for m in ms)
 van=[0]*n
 for i,j in edges:van[i]^=1<<ix[1<<i|1<<j];van[j]^=1<<ix[1<<i|1<<j]
 init=van+[1|(1<<ix[1<<j]) for j in pins];piv={}
 def red(v):
  while v and v.bit_length() in piv:v^=piv[v.bit_length()]
  return v
 while init:
  p=red(init.pop())
  if not p:continue
  k=p.bit_length();piv[k]=p
  if k<=low:
   for i in range(n):
    a=p;q=0
    while a:
     m=a&-a;a^=m;q^=1<<ix[ms[m.bit_length()-1]|1<<i]
    init.append(q)
 return len(piv), lambda v:red(v)==0
def graph(bundles):
 n=len(bundles)+1; e=[(0,n-1)]
 for j,lengths in enumerate(bundles):
  for l in lengths:
   path=[j]+list(range(n,n+l-1))+[j+1];n+=l-1;e.extend(zip(path,path[1:]))
 return n,e

b=((1,3,3),(2,4))
n,e=graph(b)
neighbors=[0]*n
for i,j in e:
 neighbors[i]|=1<<j
 neighbors[j]|=1<<i
models=[x for x in range(1<<n) if x&5==5 and all(not(x>>i&1 and (x&v).bit_count()%2) for i,v in enumerate(neighbors))]
assert models and all(x&2 for x in models)
affines=[a for a in range(1<<(n+1)) if all(((1+2*x)&a).bit_count()%2==0 for x in models)]
for d in (2,3):
 dim,P=pc(n,e,[0,2],d)
 num=sum(P(a) for a in affines)
 print("PC degree, closure dimension, affine dimension, junction pin:",d,dim,num.bit_length()-1,P(5))
 assert P(5)==(d==3)
 if d==3:assert num==len(affines)
left=sum(1<<i for i in (0,4,6,7,8,10))
assert all(bool(left>>i&1)!=bool(left>>j&1) for i,j in e)
remain=set(models);blocks=[]
while remain:
 todo=[remain.pop()];block=[]
 while todo:
  x=todo.pop();block.append(x)
  new={y for y in remain if (x^y)&left==0 or (x^y)&~left==0}
  remain-=new;todo.extend(new)
 blocks.append(block)
print("supports, one-shore components, affine invariant dimension:",len(models),len(blocks),len(affines).bit_length()-1)
assert len(blocks)==2
