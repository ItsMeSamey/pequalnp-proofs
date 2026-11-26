from pathlib import Path
from pure_sat import check
known={}
for line in Path('graphs.sat').read_text().splitlines():
 if len(a:=line.split())==4:
  p,g,r,ok=map(int,a);known[p,g,r]=ok
for line in sorted(Path('graph-queries.tsv').read_text().splitlines(),key=lambda s: (int(s.split()[1]),int(s.split()[3]))):
 i,p,g,r=map(int,line.split());ok=None
 for (pn,gn,rn),v in known.items():
  if p==pn and g==gn and ((v and rn<=r) or (not v and rn>=r)):
   ok=v;break
 if ok is None:ok=int(check(p,g,r)) if r>=0 else 0
 known[p,g,r]=ok;print(i,p,g,r,ok,flush=True)
