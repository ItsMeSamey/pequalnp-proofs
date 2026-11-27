import itertools,json
from pathlib import Path
edges=[(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
def F(s):return any(s>>a&s>>b&1 for a,b in edges)
catalog={}
for i in (0,3):
 nine=[x for x in range(1024) if x>>i&1==0]
 n={a+b-i for a,b in edges if i in (a,b)};cols=[j for j in range(10) if j!=i and j not in n]
 piv=[s for s in nine if not F(s) and F(s|1<<i)]
 e=[s for s in nine if not F(s|1<<i) and not any(s&p==s for p in piv)]
 fam=[]
 for b in range(1<<len(e)):
  add={s for j,s in enumerate(e) if b>>j&1}
  if any(s&t==s for s in add for t in set(e)-add):continue
  J=lambda s:F(s|1<<i) or s in add
  assert all(not J(s) or J(s|1<<j) for s in nine for j in range(10) if j!=i)
  vals=[sum(((x>>k)&1)<<j for k,j in enumerate(cols)) for x in range(128)]
  tt=sum(1<<k for k,s in enumerate(vals) if J(s))
  assert all(J(s)==(any(s>>j&1 for j in n) or bool(tt>>sum(((s>>j)&1)<<k for k,j in enumerate(cols))&1)) for s in nine)
  fam.append(dict(extra=sorted(add),truth=hex(tt)))
 assert len(piv)==34 and len(e)==6 and len({v['truth'] for v in fam})==25
 catalog[i]=dict(columns=cols,exceptions=e,candidate=fam)
 print(i,'pivotal',len(piv),'exceptions',e,'7-input tables',len(fam))
Path('pivot-family.json').write_text(json.dumps(catalog,indent=1)+'\n')
