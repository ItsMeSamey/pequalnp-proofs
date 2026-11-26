from pathlib import Path
from itertools import combinations
def sharpen(r):
 row,q,d,*a=r;I=a[:13];H=a[13:16];part=a[16:19];order=a[19:22];P=a[22:25];cap=a[25:38];nhot=a[-1]
 U=[m>>3 for m in I];G=[sum((i==h)<<j for j,h in enumerate(H)) for i in range(13)]
 B=[(m&7)|((1<<(3+i)) if m.bit_count()<2 else 0) for i,m in enumerate(I)]
 O=[0]*3;pre=B.copy();seen=set()
 for j in order:
  z=part[j]
  if z not in seen:O[z]=pre.copy();seen.add(z)
  for i in range(13):pre[i]|=((G[i]>>j&1)<<(16+j))
 m0=cap.copy()
 lower=[0,0,0];upper=[0,0,0];Uset=[sum(((u>>j)&1)<<i for i,u in enumerate(U)) for j in range(3)]
 for j in range(3):
  z=part[j];upper[z]=P[j]
  if H[j]>=0:lower[z]|=1<<H[j]
 groups=sorted(set(part));rep=[z for z in groups if part.count(z)>1];spare=4-sum(max(1,part.count(z)-1) for z in groups)
 while True:
  old=tuple(lower+upper+cap)
  for z in groups:
   for i in range(13):
    for k in range(13):
     if O[z][i]&~O[z][k]:continue
     if lower[z]>>i&1:lower[z]|=1<<k
     if not(upper[z]>>k&1):upper[z]&=~(1<<i)
   for j in range(3):
    if part[j]!=z:continue
    cand=upper[z]&~Uset[j]
    if cand.bit_count()<3:return
    if cand.bit_count()==3:lower[z]|=cand
   if lower[z]&~upper[z]:return
  P=[upper[z] for z in part]
  M=[sum(((s>>i)&1)<<j for j,s in enumerate(P)) for i in range(13)]
  for i in range(13):
   for k in range(13):
    if i==k or pre[i]&~pre[k]:continue
    pred=(U[i]&~G[i])&~U[k]&M[k]
    zs={part[j] for j in range(3) if pred>>j&1}
    if not zs:return
    if len(zs)==1:lower[zs.pop()]|=1<<k
  cap=[m0[i]-sum((lower[z]>>i)&1 for z in rep) for i in range(13)]
  F=[[i for i in range(13) if not ((U[i]&~G[i])&~f) and not ((M[i]&~U[i])&f)] for f in range(8)]
  mins=[1<<(4-min(4,c)) for c in cap];needed=set()
  for f in F:
   tot=sum(mins[i] for i in f)
   if tot>16:return
   for i in f:
    if cap[i]>4 or tot+mins[i]<=16:continue
    if spare:needed.add(i)
    for z in rep:
     if not(lower[z]>>i&1):upper[z]&=~(1<<i)
  if len(needed)>10:return
  if not (set([i for i in range(13) if cap[i]>0])>=needed):return
  if tuple(lower+upper+cap)==old:break
 return [row,q,d,*I,*H,*part,*order,*P,*cap,nhot],lower
if __name__=='__main__':
 res=[]
 for idx,s in enumerate(Path('maximal.tsv').read_text().splitlines()):
  t=sharpen(list(map(int,s.split())))
  if t:res.append((idx,*t))
 Path('strong.tsv').write_text(''.join(' '.join(map(str,r))+'\n' for _,r,l in res))
 Path('strong.ids').write_text(''.join(' '.join(map(str,[idx,*l]))+'\n' for idx,r,l in res))
 print(len(res),len(set(r[0] for _,r,l in res)))
