from cold7 import *
from pathlib import Path
from collections import Counter
def branch(s,t,u,m,plus,minus,ct):
 A=s|t;Y=t|u;ct['nodes']+=1
 z=tables(s,t,u,m,plus,minus)
 if not z:return
 hp,hn,p0,n0,p1,n1=z
 if conflict([(hp,hn)],A) or conflict([(p0,n0),(p1,n1)],Y):return
 unknown=sorted({x&A for x in (*E,*MIS) if not((hp|hn)>>x&1)},key=lambda x:(x.bit_count(),x))
 if unknown:
  a=unknown[0];b=1<<a
  branch(s,t,u,m,plus|b,minus,ct)
  branch(s,t,u,m,plus,minus|b,ct)
  return
 raise AssertionError(('unexcluded complete assignment',s,t,u,m,plus,minus))
for l in Path('cold7.log').read_text().splitlines():
 if l.startswith('left '):
  key=list(map(int,l.split()[1:]));ct=Counter()
  branch(*key,0,0,ct);print('done',*key,ct,flush=True)
