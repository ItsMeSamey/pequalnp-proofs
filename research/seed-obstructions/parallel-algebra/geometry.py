from collections import defaultdict
from functools import lru_cache
from itertools import combinations,combinations_with_replacement
r=defaultdict(set)
for row in open('reachable.txt'):
 a,b=map(int,row.split());r[a].add(b);r[b].add(a)
values=list(r)
def mins(S):return [x for x in range(32) if S>>x&1 and all(not (S>>(x^(1<<i))&1) for i in range(5) if x>>i&1)]
def up(S):return sum(1<<x for x in range(32) if any(x&v==v for v in S))
@lru_cache(None)
def fit(lo,hi):return set(h for h in values if h&lo==lo and h&hi==h)
def subsets(a,b,z):
 xs=mins(a&~(b|z));return [s for k in range(1,min(len(xs),3)+1) for s in combinations(xs,k) if not any(b>>(x|y)&1 for x,y in combinations(s,2))]
def main():
 failures=set();total=0
 for row in open('actual-hard.txt'):
  z,a,b,_,_=map(int,row.split())
  for aa in subsets(a,b,z):
   for bb in subsets(b,a,z):
    for i in mins(a&b&~z) or [None]:
     ai=up(aa if i is None else (*aa,i));bi=up(bb if i is None else (*bb,i))
     total+=1
     if not any(r[h]&fit(bi,b) for h in fit(ai,a)):
      failures.add((z,a,b,aa,bb,i))
 print('configurations',total,'hard',len(failures))
 for x in sorted(failures)[:10]:print(x)
 open('geo-hard.txt','w').write('\n'.join(map(repr, sorted(failures))))
if __name__=='__main__':main()
