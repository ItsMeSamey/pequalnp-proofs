from edge import *
def main(a,b):
 sig=[(bool(a&1<<j),bool(b&1<<j)) for j in range(7)]
 active=[(lc[a] if x else alln)&(lc[b] if y else alln) for x,y in sig]
 safe=[sum(1<<p for p in inside(s) if points[p]&active[j]) for j,s in enumerate(ss)]
 hit=[pc[s] for s in safe]
 ex=[(s^z).bit_count() for s,z in zip(ss,safe)]
 for j in range(7):
  other=set(range(7))-{j}
  w=[hit[v] for v in other]+[hit[v]&hit[u] for v,u in combinations(other,2) if sig[v]!=sig[u]]
  if not all(all(m&g for m in pairs[j]) for g in w):return 'geometry'
 r=sum(ex);c=(a|b).bit_count()-2+bool(a&b)
 pen=max((max(min(e,8-e-ex[i]-ex[j]) for e in range(12)) for i,j in product(range(7),repeat=2) if sig[i]==(1,0) and sig[j]==(0,1)),default=0)
 return 'all' if r+pen<=c+2 else 'distinct' if r<=c+2 else 'budget'
if __name__=='__main__':
 C=Counter()
 for a,b in combinations([s for s in range(1,128) if s.bit_count()>=2],2):
  h=failures(a,b)
  if not h: continue
  c=(a|b).bit_count()-2+bool(a&b)
  C[c,len(h),main(a,b)]+=1
 print(C)
