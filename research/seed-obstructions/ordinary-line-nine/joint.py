from noand import *
def joint(a,b):
 sig=[(bool(a&1<<j),bool(b&1<<j)) for j in range(7)]
 active=[(lc[a] if x else alln)&(lc[b] if y else alln) for x,y in sig]
 safe=[sum(1<<p for p in inside(s) if points[p]&active[j]) for j,s in enumerate(ss)]
 c=(a|b).bit_count()-2+bool(a&b)
 missing=[]
 for group in range(1,128):
  g=[j for j in range(7) if group>>j&1]
  un=[j for j in g if not any(k!=j and all(x<=y for x,y in zip(sig[k],sig[j])) for k in g)]
  if len(un)<2:continue
  knownneg=union(active[j]&pc[safe[j]] for j in g)
  certified=sum(1<<p for p in range(13) if points[p]&knownneg)
  sq=[s|(certified&ss[j]) for j,s in enumerate(safe)]
  ex=[(s^z).bit_count() for s,z in zip(ss,sq)]
  r=sum(ex);i,j=un
  pen=max(min(e,8-e-ex[i]-ex[j])for e in range(12))
  if r+pen>c+2: missing.append((group,r,pen))
 return missing
if __name__=='__main__':
 d=Counter()
 for a,b in combinations([s for s in range(1,128) if s.bit_count()>=2],2):
  if not failures(a,b) or main(a,b)!='distinct':continue
  misses=joint(a,b);d[len(failures(a,b)),len(misses)]+=1
 print(d)
