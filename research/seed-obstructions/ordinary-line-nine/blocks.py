from edge import *
def evaluate(a,b,blocks):
 nodes={t for e in blocks for t in e}
 assert len(nodes)==2*len(blocks)
 sig=[(bool(a&1<<j),bool(b&1<<j)) for j in range(7)]
 active=[(lc[a] if x else alln)&(lc[b] if y else alln) for x,y in sig]
 safe=[sum(1<<p for p in inside(s) if points[p]&active[j]) for j,s in enumerate(ss)]
 hit=[pc[s] for s in safe]
 ex=[(s^z).bit_count() for s,z in zip(ss,safe)]
 outside=[j for j in range(7) if j not in nodes]
 repairs=sum(ex)
 for t,u in blocks:
  for x,y in [(t,u),(u,t)]:
   if not all(m&active[y]&hit[y] for m in pairs[x]):repairs+=3-ex[x]
 for j in outside:
  labels=[x for x in outside if x!=j]
  unionhits=[hit[t]|hit[u] for t,u in blocks]
  witnesses=[hit[v] for v in labels]+unionhits
  witnesses += [hit[v]&w for v in labels for w in unionhits]
  witnesses += [hit[v]&hit[w] for v,w in combinations(labels,2) if sig[v]!=sig[w]]
  if not all(all(m&g for m in pairs[j]) for g in witnesses):return 'witness'
 cost=(a|b).bit_count()-2+bool(a&b)
 pen=max((max(min(e,8-e-ex[i]-ex[j]) for e in range(12)) for i,j in product(outside,repeat=2) if sig[i]==(1,0) and sig[j]==(0,1)),default=0)
 return 'all' if repairs+pen<=cost+2 else 'distinct' if repairs<=cost+2 else 'budget'
if __name__=='__main__':
 cc=Counter()
 for a,b in combinations([s for s in range(1,128) if s.bit_count()>=2],2):
  h=failures(a,b)
  if len(h)!=2: continue
  disjoint=not(set(h[0])&set(h[1]))
  ok=[evaluate(a,b,[e]) for e in h]
  if disjoint:ok+=[evaluate(a,b,h)]
  cc[disjoint,tuple(sorted(ok))]+=1
 print(cc)
