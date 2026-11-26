from itertools import combinations, permutations
from collections import defaultdict
E=[(i,j) for j in range(5) for i in range(j)]
perms=list(permutations(range(5)))
def transform(m,p):
 return sum(1<<E.index(tuple(sorted((p[i],p[j])))) for b,(i,j) in enumerate(E) if m>>b&1)
def degs(m):
 return [sum(bool(m>>b&1) for b,e in enumerate(E) if i in e) for i in range(5)]
def connected(m):
 reach={0}
 for _ in range(4):
  for k,(i,j) in enumerate(E):
   if m>>k&1 and (i in reach or j in reach):reach.update([i,j])
 return len(reach)==5
forb={transform(d,p) for d in (237,254) for p in perms}
by=defaultdict(list)
for m in range(1,1023):
 if not connected(m) or m!=min(transform(m,p) for p in perms):continue
 d=degs(m); n=m.bit_count()
 if n<5:continue
 strip=[i for i in range(5) if n-d[i]>=5]
 floor=max(d)==4 or any(m&f==f for f in forb)
 by[n].append((m,strip,floor))
for n,B in by.items():print(n,B)
wins=[]
for n in (5,6,7):
 for r in by[n]:
  for l in by[14-n]:
   if n==7 and r[0]>l[0]:continue
   def closes(R,L):
    if not L[2]:return False
    t=L[0].bit_count()
    if t>=6:return bool(R[1])
    d=degs(R[0])
    return any(sum(d[y]==4 for y in range(5) if y!=x)>=2 for x in R[1])
   if closes(r,l) or closes(l,r):wins.append((r[0],l[0]))
print('excluded',len(wins),wins)
