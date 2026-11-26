from pathlib import Path
from itertools import combinations
exec(Path('coverage.py').read_text().split('hist=Counter')[0])
profiles={}
out=[]
for row in Path('allbanks').read_text().splitlines():
 s,r,lc,bad=map(int,row.split());active=[]
 for i,T in enumerate(stars):
  active.append(sum(1<<p for p in range(13) if T>>p&1 and any(n>>p&1 and (not(s>>i&1) or n>>13&s) and (not(r>>i&1) or n>>13&r) for n in ng)))
 key=tuple(active)
 if key not in profiles:profiles[key]=len(profiles)+20000
 out.append((s,r,lc,profiles[key]))
for active,code in profiles.items():
 with open('neg.'+str(code),'w') as f:
  print(*(stars[i]^active[i] for i in range(7)),file=f)
  for t,T in enumerate(stars):
   for a in [i for i in range(13) if not T>>i&1]:
    x=(1<<a)|(1<<(13+t));bank={sum((bool(n&V)<<v) for v,V in enumerate(active)) for n in ng if n&x==x}
    m=[v for v in bank if not any(v!=w and v&w==v for w in bank)];print(len(m),*m,file=f)
Path('allsingle').write_text('\n'.join(' '.join(map(str,row)) for row in out)+'\n')
complete={tuple(map(int,row.split()[:2])) for row in Path('banks').read_text().splitlines()}
Path('singlebanks').write_text('\n'.join(' '.join(map(str,row)) for row in out if row[:2] in complete)+'\n')
print('profiles',len(profiles))
