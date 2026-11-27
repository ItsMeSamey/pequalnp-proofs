from collections import Counter
from itertools import product

def cases():
 for k in range(3,23):
  for x in range(23-k):
   for z in range(1,23-k-x):
    for b in range(2,23-k-x-z):
     for w in range(1,23-k-x-z-b):
      budget=k+x+z+b+w+1
      for r,s,h in product(*(range(n.bit_length()) for n in [k+x+w,b+w,k+z])):
       deficit=2*(r+s+h)-budget
       if deficit>0: yield k,x,z,b,w,r,s,h,deficit
if __name__=='__main__':
 cs=list(cases())
 print(len(cs),Counter(v[-1] for v in cs),sorted({v[0] for v in cs}))
 print(Counter((v[5],v[6],v[7]) for v in cs))

def pair_options(a,b,c,r,s):
 # a,b are total clauses of terms; c shared.
 savings=0
 for n,h,m,g in ((a,r,b,s),(b,s,a,r)):
  if h>=2 and c>2*(n-2**h):
   if g>h:return []
   savings=max(savings,g)
 if r<3 and s<3:return [savings]
 if s>r:a,b,r,s=b,a,s,r
 opts=[]
 if a+b-c>=2**r+2**s:opts.append(0)
 if s<3:
  if a-c>=2**r:opts.append(0)
  for e in range(1,s+1):
   if a-c>=2**r-2**(r-e) and a+b-c>=2**r+(2**(s-e) if s>e else 0):
    opts.append(e)
 return [max(savings,x) for x in opts]

if __name__=='__main__':
 rem=[]
 for v in cases():
  k,x,z,b,w,r,s,h,deficit=v
  a=k+x+w
  o=pair_options(a,k+z,k,r,h)
  p=pair_options(a,b+w,w,r,s)
  if o and p and max(min(o),min(p))<deficit:rem.append(v)
 print('remaining',len(rem));print(*rem,sep='\n')
