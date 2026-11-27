from pathlib import Path
from zipfile import ZipFile
from tempfile import TemporaryDirectory
from ast import literal_eval
import sys,json,os
root=Path(__file__).resolve().parent
roster=set(map(int,(root.parent/'cumulative-0340/t0-remaining-26.ids').read_text().split()))
Q={2:5,8:1,16:2,32:3}
required={int(l.split(' ',1)[0]):sum(1<<Q[q] for q,_,_ in literal_eval(l.split(' ',1)[1]))for l in (root/'more-pivots.log').read_text().splitlines()[1:-1]}
with TemporaryDirectory() as d:
 with ZipFile('/workspace/scratch/syn_quotients/t0-both74-six-final-five.zip')as z:z.extractall(d)
 sys.path.insert(0,d)
 from realcore import Source,ALL,pass_budget
 from cuts import load
 s=object.__new__(Source);s.P,s.N=load(());s.pts=ALL
 s.stars=tuple({p&8191 for p in s.P if p>>(13+j)&1}for j in range(7))
 s.inc={p:sum(1<<u for u in range(7) if p in s.stars[u])for p in s.pts}
 with ZipFile('/workspace/scratch/synthesis_new/allpresent-spine274.zip')as z:rows=list(map(json.loads,z.read('remaining.jsonl').splitlines()))
 for i,t,e,R,C in rows:
  if i not in roster:continue
  s.bank(C,8191^R); demand=required.get(i,0);k=34-(R.bit_count()+7+len(C))
  surviving=[o for o in range(128) if o&demand==demand and pass_budget(*s.roles(o,k)[2:])]
  print(i,demand,surviving)
