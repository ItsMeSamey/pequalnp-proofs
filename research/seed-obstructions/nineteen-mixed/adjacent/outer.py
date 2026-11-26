from verify import *
from collections import Counter
def profile(a,b,t,c):
 outside=set(range(7))-{t,c};sig=[(bool(a>>j&1),bool(b>>j&1))for j in range(7)]
 active=[(lc[a] if x else alln)&(lc[b] if y else alln) for x,y in sig]
 sq=[sum(1<<p for p in inside(s) if points[p]&active[j]) for j,s in enumerate(ss)]
 hit=[pc[s] for s in sq]
 geo=all(all(m&hit[t]&hit[k] for m in pairs[j]) for j in outside for k in outside-{j})
 result=[]
 for j in outside:
  forced=union(active[k]&hit[k] for k in (t,c,j))
  cert=sum(1<<x for x in range(13) if points[x]&forced)
  repair=sum((ss[k]&~(sq[k]|cert)).bit_count() for k in outside|{c})+3
  result.append(repair)
  if j not in inside(b&~a):assert repair==3
 assert geo
 return geo,tuple(sorted(result))
if __name__=='__main__':
 C=Counter()
 for a,b in combinations([x for x in range(128) if x.bit_count()==2],2):
  if not a&b:continue
  for s,r in ((a,b),(b,a)):
   t,=inside(s&~r);c,=inside(s&r)
   C[profile(s,r,t,c)]+=1
 print(C)
