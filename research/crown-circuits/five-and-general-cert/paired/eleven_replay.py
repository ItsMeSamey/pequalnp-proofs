import os
from pathlib import Path
from tempfile import TemporaryDirectory
import json,subprocess
from eleven_full import test
D=json.loads(Path('eleven-control.json').read_text());full=65535;reach=[0]*(D['n']+len(D['gates']));reach[D['output']]=full
for x in range(1<<D['n']):
    v=[bool(x>>i&1) for i in range(D['n'])]
    for op,a,b in D['gates']:v.append((v[a] and v[b]) if op=='and' else (v[a] or v[b]))
    assert v[D['output']]==(x.bit_count()>=2)
print('physical truth table',1<<D['n'],'passed',flush=True)
branches=[];j=0
for t in range(len(D['gates'])-1,-1,-1):
 op,a,b=D['gates'][t];w=reach[D['n']+t]
 if op=='or':reach[a]|=w;reach[b]|=w
 else:
  pos=sum(1<<x for x in range(16) if (x>>j)&1);p=w&pos;q=w&(full^pos);branches.extend([p,q]);reach[a]|=p;reach[b]|=q;j+=1
C=0
for r in reach[:D['n']]:
 k=next(i for i in range(16) if not(r>>i&1));C|=1<<k
assert C.bit_count()==11
for solver in ('cadical195','glucose4'):
 r,n=test(full^C,branches,17,solver);print('27-gate control',solver,r,n,flush=True);assert r
for i,line in enumerate(s for s in Path('eleven_budget.out').read_text().splitlines() if s.startswith('witness ')):
 h,*b=map(int,line.split()[1:])
 r,n=test(h,b,15,'glucose4');assert r is False
 with TemporaryDirectory() as tmp:
  path=Path(tmp);r,k=test(h,b,15,'cadical195',path);assert r is False
  ans=subprocess.run([os.environ.get('DRAT_TRIM','drat-trim'),str(path/'case.cnf'),str(path/'case.drat')],capture_output=True,check=True)
  assert b's VERIFIED' in ans.stdout
 print(i,h,'glucose',n,'cadical',k,'DRAT verified',flush=True)
