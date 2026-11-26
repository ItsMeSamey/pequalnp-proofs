"""Replay the 50 two-ordinary-star representatives using an external cost-eleven point-bank input."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import subprocess
import sys
import tempfile
from verify import h,here,raw,stars,sym_points
def read(p):
    return {tuple(sorted(map(int,row.split()))) for row in p.read_text().splitlines()}
all_points=read(Path(sys.argv[1]))
low=read(here/'cost-ten-star-local.txt')
assert low<=all_points and len(all_points)==2668
rows=Counter()
for p in all_points-low:
    if len(set(stars)&set(p))<2:continue
    images=sym_points(p)
    best=min(q for q,g in images)
    actions=[g for q,g in images if q==best]
    for i,j in combinations(range(7),2):
        if len((set(stars)-{stars[i],stars[j]})&set(p))<2:continue
        x=(1<<i)|(1<<j)
        rows[best,min(g[x] for g in actions)]+=1
assert (len(rows),sum(rows.values()))==(50,1020)
with tempfile.TemporaryDirectory() as d:
    binary=Path(d)/'frontier'
    subprocess.run(['c++','-O3','-std=c++17',here/'frontier.cpp','-o',binary],check=True)
    payload=h+'\n50 11 8 3\n'+''.join(' '.join(map(str,(*p,*raw,x)))+'\n' for p,x in sorted(rows))
    r=subprocess.run([binary],input=payload,text=True,stdout=subprocess.PIPE,check=True)
    depths=list(map(int,r.stdout.split()))
    assert len(depths)==50 and max(depths)<=21
    print(len(rows),sum(rows.values()),sorted(Counter(depths).items()))
