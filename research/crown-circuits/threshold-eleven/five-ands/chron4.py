from itertools import product
def profiles(bs=()):
 if len(bs)==8:
  yield bs
  return
 j=len(bs)//2
 half=sum(1<<x for x in range(16) if (x>>j)&1)
 pool={0}
 for b in bs:pool.update(a|b for a in list(pool))
 for u in (pool|{65535})-{0}:
  yield from profiles(bs+(u&half,u&(65535^half)))
seen=set()
for b in profiles():
 traces={tuple(x>>j&1 for x in b):j for j in range(16)}
 if len(traces)<10:continue
 points=[j for _,j in sorted(traces.items())]
 source=tuple(sorted(set(sum((m>>j&1)<<i for i,j in enumerate(points)) for m in b)))
 key=(len(points),source)
 if key in seen:continue
 seen.add(key);print(0,len(points),len(source),*source)
