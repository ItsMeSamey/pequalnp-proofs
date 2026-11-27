from itertools import product,combinations_with_replacement
from pathlib import Path
flip=(0,2,1,3)
cols=sorted({min(c,tuple(flip[x] for x in c)) for c in product(range(3),repeat=3)})
late=sorted({min(c,tuple(flip[x] for x in c)) for c in product(range(4),repeat=2)})
rows=[]
for cs in combinations_with_replacement(cols,3):
 base=[sum(c[i]<<(2*j) for j,c in enumerate(cs)) for i in range(3)]
 if not base[2]:continue
 for a in (0,1,3):
  for b,c in late:
   T=[base[0]|(a<<8)|(b<<10),base[1]|(c<<10),base[2]]
   if not all(T):continue
   valid=True
   for m in T:
    for k,h in enumerate(T,3):
     if (m>>(2*k))&3==3:m|=h
    if m&(m>>1)&21:valid=False
   if valid:rows.append(tuple(T))
rows.sort(key=lambda t:(sum(x.bit_count() for x in set(t)),t))
p=Path(__file__).with_name('t8-three-profiles.tsv');p.write_text(''.join('%d %d %d\n'%r for r in rows));print(len(rows))
keep=[]
for row in rows:
 groups=[]
 for mask in row:
  old=[h for h in groups if h&mask]
  groups=[h for h in groups if h not in old]
  for h in old:mask|=h
  groups.append(mask)
 rank=sum(h.bit_count()-1 for h in groups)
 if rank<=4:keep.append(row)
p.with_name('t8-three-rank.tsv').write_text(''.join('%d %d %d\n'%r for r in keep))
print('rank at most four',len(keep))
