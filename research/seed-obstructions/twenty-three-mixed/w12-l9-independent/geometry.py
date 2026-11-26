from pathlib import Path
from itertools import combinations_with_replacement
import sys
sys.path.insert(0,str(Path(sys.argv[3]).resolve()))
from sample import move,symmetries,raw
data=Path(sys.argv[2])
L=[tuple(map(int,z.split()))for z in (data/'lines').read_text().splitlines()]
P=[tuple(map(int,z.split()))for z in(data/'points').read_text().splitlines()]
group=symmetries()
idx={w:i for i,w in enumerate(L)}
gL=[[idx[tuple(sorted(t[m]for m in w))]for w in L] for _,t in group]
tab=Path(sys.argv[1])/'twelve-eight.zip'
from zipfile import ZipFile
rows=[tuple(map(int,z.split()))for z in ZipFile(tab).read('twelve-eight/banks-through-eight.txt').decode().splitlines()]
masks={x for row in rows for x in row[:-1]}; maps=[{x:move(x,p)for x in masks}for p,_ in group]
prices={}
for row in rows:
 key=min(tuple(sorted(t[x]for x in row[:-1]))for t in maps)
 prices[key]=min(prices.get(key,99),row[-1])
assert set(P)==set(prices)
from collections import Counter
print('point orbit minima',Counter(prices.values()),flush=True)
def cost(w):
 a=[v for v in set(w) if v.bit_count()>=2]
 if len(a)==3:return 3
 return len(w)-len(set(w)-{0})+sum(v.bit_count()-1 for v in a)-max(0,((a[0]&a[1]).bit_count()-1) if len(a)==2 else 0)
costs=list(map(cost,L))
for c in range(5,9):
 seen=set()
 for i,w in enumerate(P):
  if prices[w]!=c:continue
  stab=[j for j,(p,t)in enumerate(group) if tuple(sorted(move(x,p)for x in w))==w]
  leaders={min(gL[j][k]for j in stab)for k,price in enumerate(costs)if price<=10-c}
  seen.update((i,k)for k in leaders)
 listed={tuple(map(int,z.split()))for z in(data/f'c{c}').read_text().splitlines()}
 physical={p for p in listed if costs[p[1]]<=10-c}
 assert physical==seen
 print(c,'paired physical orbits',len(seen),flush=True)
