from support_cases import cases
from itertools import permutations,combinations
from collections import Counter
from pathlib import Path
def gen():
 for row,q,d,I,B,U,H,G,req,disj in cases():
  for part in ((0,1,2),(0,0,1),(0,1,0),(0,1,1),(0,0,0)):
   groups=sorted(set(part));count=[part.count(z) for z in groups];spare=4-sum(max(1,k-1) for k in count)
   if any(sum(1 for j in range(3) if part[j]==z and H[j]<0)>1 for z in groups):continue
   for order in permutations(range(3)):
    P=[0]*3;seen=set();pre=B[:];good=True
    for j in order:
     z=part[j]
     if z not in seen:
      neg=[k for k in range(13) if any(part[l]==z and U[k]>>l&1 and H[l]!=k for l in range(3))]
      mask=sum((not any(not(pre[k]&~pre[v]) for v in neg))<<k for k in range(13))
      for l in range(3):
       if part[l]==z:P[l]=mask
      seen.add(z)
     if (H[j]>=0 and not(P[j]>>H[j]&1)) or sum(bool(P[j]>>i&1) and not(U[i]>>j&1) for i in range(13))<3:good=False;break
     pre=tuple(p|(((g>>j)&1)<<(16+j)) for p,g in zip(pre,G))
    if not good:continue
    M=[sum(((s>>i)&1)<<j for j,s in enumerate(P)) for i in range(13)]
    if any(r&~m for r,m in zip(req,M)) or any(not(M[i]&a) for i,a in disj):continue
    cap=[2+(I[i]&7).bit_count()-(U[i]&~G[i]).bit_count()+spare for i in range(13)]
    # Ignore the nonpositive cost of a partner shared across several gates.
    F=[[i for i in range(13) if not ((U[i]&~G[i])&~f) and not ((M[i]&~U[i])&f)] for f in range(8)]
    masses=[sum(1<<(4-min(4,cap[i])) for i in f) for f in F]
    if max(masses)>16:continue
    dcount=d.bit_count();nmixed=26-sum(m.bit_count() for m in I)
    nhot=max(0,3+(max(0,4+dcount-nmixed)+1)//2-dcount)
    ok=True
    for a,b in combinations(range(13),2):
     query=B[a]|B[b];probes=list(B);value={}
     for j in order:
      z=part[j]
      if z not in value:value[z]=not any(not(P[j]>>k&1) and not(query&~probes[k]) for k in range(13))
      if value[z] and (U[a]|U[b])>>j&1:query|=1<<(16+j)
      for k in range(13):probes[k]|=((G[k]>>j&1)<<(16+j))
     if any(not(query&~v) for v in probes):ok=False;break
    if ok:yield row,q,d,I,H,part,order,tuple(P),tuple(cap),nhot
if __name__=='__main__':
 found=set(gen());rows={r[0] for r in found}
 print(len(found),len(rows),Counter(len(set(r[5])) for r in found))
 Path('maximal.tsv').write_text(''.join(' '.join(map(str,[row,q,d,*I,*H,*part,*order,*P,*cap,nhot]))+'\n' for row,q,d,I,H,part,order,P,cap,nhot in sorted(found)))
