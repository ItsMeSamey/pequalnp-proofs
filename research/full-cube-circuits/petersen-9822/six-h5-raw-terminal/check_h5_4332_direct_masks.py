"""Independent fixed-width placement scan and three-product union check. Output is index, placements, passes, maximum edge coverage."""
from h5_three_sink_leak_sets import N,EDGES,CASES
R=1023; W=(4,3,3,2); by={k:[i for i in range(1,1024) if i.bit_count()==k] for k in set(W)}
def ok(a,b):return (a&b).bit_count()<=1
for ix in (2,8,11,18,29,44,65,114):
 i,j=CASES[ix];m=R^N[i];n=R^N[j]; candidates=set()
 for y in [s for s in range(1,1024) if s&(m&n)==s]:
  if y.bit_count()>4:continue
  for a in by[2]+by[3]+by[4]:
   if a|y!=m:continue
   for b in by[2]+by[3]+by[4]:
    if b|y!=n or not ok(a,b):continue
    rest=list(W)
    for t in (a,b):
     if t.bit_count() not in rest:break
     rest.remove(t.bit_count())
    else:
     for c in by[rest[0]]:
      if not all(ok(c,v) for v in (a,b)):continue
      for d in by[rest[1]]:
       if not all(ok(d,v) for v in (a,b,c)):continue
       if not any(y&t==y for t in (a,b,c,d)):continue
       ab=tuple(sorted((a,b)));cd=tuple(sorted((c,d)))
       for sc,h in [((*ab,*cd),1024),((*cd,*ab),2048)]:
        candidates.add((*sc,h|y))
 expected={x for x in candidates if x[-1]&1024}
 rows=(*EDGES,*N)
 raw=[sum(1<<i for i,x in enumerate(rows) if x&v) for v in range(1024)]
 target=8191|sum(1<<(13+k) for k in (i,j))
 pieces={s:[v for v in range(1,1024) if (v&s)==v] for bucket in by.values() for s in bucket}
 best=0;feasible=0
 for a,b,c,d,u in expected:
  available={raw[1<<k] for k in range(10)}
  for s in (a,b,c,d):
   available.update(raw[z] for z in pieces[s])
  h=raw[a]&raw[b];q=raw[c]&raw[d]
  available.update([h,q,h|raw[u&1023]])
  offers={x&y for x in available for y in available if (x&y)&~target==0 and (x&y)>>13 and (x&y)&8191}
  reach={0}
  for step in range(3):reach|={s|g for s in reach for g in offers}
  feasible+=target in reach
  best=max(best,max((s&8191).bit_count() for s in reach))
 print(ix,len(expected),feasible,best,flush=True)
