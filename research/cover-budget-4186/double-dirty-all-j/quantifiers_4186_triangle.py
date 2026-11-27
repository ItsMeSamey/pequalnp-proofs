from itertools import product
from collections import Counter
from bounds_4186_shared_defects import pair_options

def cases(counts):
 for w in range(1,22):
  for k in range(2,22-w):
   for l in range(2,22-w-k):
    for x in range(22-w-k-l):
     for y in range(22-w-k-l-x):
      for z in range(22-w-k-l-x-y):
       budget=w+k+l+x+y+z+2
       ns=(w+k+x,w+l+y,k+l+z)
       for rs in product(*(range(n.bit_length()) for n in ns)):
        deficit=2*sum(rs)-budget
        if max(rs)<3 or deficit<=0:continue
        pairs=[pair_options(ns[i],ns[j],c,rs[i],rs[j]) for i,j,c in ((0,1,w),(0,2,k),(1,2,l))]
        counts["positive deficit"] += 1
        if not all(pairs):
         counts["incompatible pair"] += 1
         continue
        if max(min(p) for p in pairs)>=deficit:
         counts["one pair covers deficit"] += 1
         continue
        yield (w,k,l,x,y,z),ns,rs,deficit
if __name__=='__main__':
 counts=Counter()
 cs=list(cases(counts))
 print(counts)
 print(len(cs),Counter(x[2] for x in cs),Counter(x[3] for x in cs))
 print(*cs[:15],sep='\n')
