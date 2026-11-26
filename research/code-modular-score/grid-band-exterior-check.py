from itertools import permutations,combinations
def partitions(n,edges):
 ps={tuple(range(n))}
 for u,v in edges:
  nxt=set(ps)
  for a in ps:
   if a[u]!=a[v]:
    z=min(a[u],a[v]);y=max(a[u],a[v]);nxt.add(tuple(z if q==y else q for q in a))
  ps=nxt
 return ps
def span(a):
 f={0}
 for x in a:f|={v^x for v in f}
 return sum(1<<v for v in f)
def spec(ps,l):
 out=set()
 for p in ps:
  b={}
  for x,c in zip(l,p):b[c]=b.get(c,0)^x
  out.add(span(b.values()))
 return out
for n,top,bot in [(4,[0,1,2,3],[0,2,4,6]),(5,[1,1,2,2,0],[2,2,4,4,0])]:
 pe=[(i,i+1) for i in range(n-1)];P=partitions(2*n,pe+[(i+n,j+n) for i,j in pe]+[(i,i+n) for i in range(n)])
 Q=partitions(n,pe)
 for b in sorted(set(permutations(bot))):
  for t in sorted(set(permutations(top))):
   v=t[::-1]
   if t>=v:continue
   f=spec(P,t+b);g=spec(P,v+b)
   if f!=g:
    print(n,t,v,b,sorted(f-g),sorted(g-f),len(f),len(g),spec(Q,t)==spec(Q,v));quit()
