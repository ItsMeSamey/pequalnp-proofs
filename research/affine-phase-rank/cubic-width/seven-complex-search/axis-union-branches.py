from itertools import product

p=65537; J=(1,256,p-1,p-256)
def dictionary():
 D=[]
 for mask in range(1,256):
  S=[i for i in range(8) if mask>>i&1];o=S[0]
  coords=[0]
  for v in [i^o for i in S]:
   if v not in coords: coords += [i^v for i in coords]
  if len(coords)!=len(S):continue
  d=len(S).bit_length()-1
  for aa in product(range(4),repeat=d):
   for hh in product(range(2),repeat=d*(d-1)//2):
    f=[0]*8
    for j,v in enumerate(coords):
     x=[(j>>i)&1 for i in range(d)]
     e=sum(a*b for a,b in zip(aa,x))+2*sum(a*b for a,b in zip(hh,[x[i]*x[k] for i in range(d) for k in range(i)]))
     f[o^v]=J[e%4]
    D.append(f)
 return D
def key(a):
 k=next(v for v in a if v)
 return tuple(t*pow(k,-1,p)%p for t in a)
D=dictionary()
ids={key(a):i for i,a in enumerate(D)}
groups=[min(ids[key([a[x^u]*(1-2*((x&v).bit_count()%2)) for x in range(8)])] for v in range(8) for u in range(8)) for a in D]

ts=[(2,0,1,0,0,1),(2,1,3,0,0,1),(2,2,2,0,0,1)]
print(len(D))
for a in D:print(*a)
print(*groups)
for branch in range(2):
 v=[0]*8
 for A,B,C in product(range(8),repeat=3):
  count=(A,B,C).count(0)
  residual=(-1)**count-(1-2*count)
  assert residual==4*(count>=2)
  phase=2*branch*(A&1)
  for block,(a,b,c,h,k,l) in zip((A,B,C),ts):
   x,y,z=[block>>i&1 for i in range(3)]
   phase+=a*x+b*y+c*z+2*(h*x*y+k*x*z+l*y*z)
  v[A^B^C]+=(residual//4)*J[phase%4]
 print(*(t%p for t in v))
