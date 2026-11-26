from edge import *
counts=Counter()
for s in (m for m in range(1,128) if m.bit_count()==2):
 a,b=inside(s);x=ss[a]&ss[b]
 for t,j in [(a,b),(b,a)]:
  for l in range(7):
   if l in (a,b):continue
   special={t,l};ordinary=set(range(7))-special
   q=[star if k!=j else (star&~x) for k,star in enumerate(ss)]
   bad1=bad2=bad3=0
   for h in range(7):
    for v in ordinary-{h}:
     for p1,p2 in combinations(inside(8191^ss[h]),2):
      n=lines[h]&points[p1]&points[p2]
      if not n&pc[q[v]]:bad1+=1
   for h in special:
    u=next(iter(special-{h}))
    for v in ordinary:
     for p in inside(8191^ss[h]):
      for r1,r2 in combinations(inside(ss[u]&~ss[h]),2):
       if not lines[h]&points[p]&pc[q[v]]&(points[r1]|points[r2]):bad2+=1
   counts[bool(bad1),bool(bad2)]+=1
print(counts)
