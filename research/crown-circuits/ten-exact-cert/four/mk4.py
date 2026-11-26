from itertools import product
def scan(k,n):
 for p in range(1,k+1):
  d=k-p
  options=[[(a,b)for a in range(1<<min(i,d))for b in range(a,1<<min(i,d))]for i in range(k)]
  seen=set()
  for dep in product(*options):
   clauses=set()
   for pat in range(1<<k):
    live=((1<<p)-1)<<d;m=0
    for i in reversed(range(k)):
     if live>>i&1:
      b=pat>>i&1;m|=1<<(2*i+b);live|=dep[i][b]
    clauses.add(m)
   cs=sorted(c for c in clauses if not any(q!=c and not q&~c for q in clauses))
   if len(cs)<n:continue
   good=0
   for c in cs:
    raw=((1<<(2*k))-1)^c;st=0
    for i,(a,b) in enumerate(dep):
     if (raw>>(2*i)&1 or st&a) and (raw>>(2*i+1)&1 or st&b):st|=1<<i
    good|=st
   if (good&((1<<d)-1))!=(1<<d)-1:continue
   bases=tuple(sorted(set(sum(1<<j for j,c in enumerate(cs) if c>>b&1) for b in range(2*k))-{0}))
   desc=(len(cs),bases)
   if desc in seen:continue
   seen.add(desc)
   print(p,len(cs),len(bases),*bases)
if __name__=='__main__':scan(4,10)
