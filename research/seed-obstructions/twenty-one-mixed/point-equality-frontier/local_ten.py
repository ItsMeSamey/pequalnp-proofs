"""Twenty-one mixed gates, eleven point wires, and a ten-gate star-local point bank."""
import sys,tempfile,subprocess
from collections import Counter
from pathlib import Path
from itertools import combinations_with_replacement
from verify import here,raw,h,sym_points,line_price
def check(l):
 points=[tuple(map(int,s.split())) for s in (here/'cost-ten-star-local.txt').read_text().splitlines()]
 assert len(set(points))==354
 if l==7:lines=[raw]
 elif l==8:lines=[tuple(sorted((*raw,m))) for m in range(128) if m.bit_count()<=3]
 elif l==9:lines=sorted({tuple(sorted((*raw,a,b))) for a,b in combinations_with_replacement(range(128),2) if line_price(a,b)<=2})
 else:raise ValueError(l)
 rows=Counter()
 for p in points:
  imgs=sym_points(p);best=min(q for q,g in imgs);stems=[g for q,g in imgs if q==best]
  for f in lines:rows[best,min(tuple(sorted(g[m] for m in f)) for g in stems)]+=1
 assert (len(rows),sum(rows.values()))=={7:(23,354),8:(1070,22656),9:(8466,191160)}[l]
 return rows
with tempfile.TemporaryDirectory() as t:
 binary=Path(t)/'frontier'
 subprocess.run(['c++','-std=c++17','-O3','-march=native',here/'frontier.cpp','-o',binary],check=True)
 for l in map(int,sys.argv[1:] or ['7','8','9']):
  rows=check(l);k=11-l
  data=h+'\n'+f'{len(rows)} 11 {l} {k}\n'+''.join(' '.join(map(str,(*p,*f)))+'\n' for p,f in rows)
  r=subprocess.run([binary],input=data,text=True,stdout=subprocess.PIPE,check=True)
  empty=list(map(int,r.stdout.split()));assert len(empty)==len(rows) and max(empty)<=21
  print(l,k,len(rows),sum(rows.values()),Counter(empty),flush=True)
