from collections import defaultdict, Counter
from functools import lru_cache
from itertools import combinations
def up(S,n):return sum(1<<x for x in range(32) if any(x&v==v for v in S))
def minimal(mask,n):return [x for x in range(1<<n) if mask>>x&1 and all(not mask>>(x^(1<<i))&1 for i in range(n) if x>>i&1)]
def subsets(a,b,z,n):
 xs=minimal(a&~(z|b),n)
 return [s for k in range(1,min(len(xs),3)+1) for s in combinations(xs,k) if not any(b>>(x|y)&1 for x,y in combinations(s,2))]
def main():
 counts=Counter();left=[]
 for n in range(1,6):
  r=defaultdict(set)
  for row in open('reach.'+str(n)):
   a,b=map(int,row.split());r[a].add(b);r[b].add(a)
  vals=list(r)
  @lru_cache(None)
  def fit(lo,hi):return set(x for x in vals if x&lo==lo and x&hi==x)
  def match(lo,a,lv,b):return any(r[x]&fit(lv,b) for x in fit(lo,a))
  for row in open('seq-triples'):
   z,a,b,nr=map(int,row.split())
   if n!=nr:continue
   if b in r[a]:continue
   sa=up(minimal(a&~z,n),n);sb=up(minimal(b&~z,n),n)
   if match(sa,a,sb,b):continue
   for aa in subsets(a,b,z,n):
    for bb in subsets(b,a,z,n):
     for c in minimal(a&b&~z,n):
      ai=up((*aa,c),n);bi=up((*bb,c),n)
      if match(ai,a,bi,b):continue
      if len(aa)==1 or len(bb)==1:
       X,Y=(aa,bb) if len(aa)==1 else (bb,aa)
       if len(Y)<=2 and all((X[0]^w).bit_count()+len(Y)-1<=n for w in Y):continue
      left.append((n,z,a,b,aa,bb,c));counts[n]+=1
  print(n,counts[n],flush=True)
 print('left',len(left))
 open('seq-hard','w').write('\n'.join(map(repr,left)))
if __name__=='__main__':main()
