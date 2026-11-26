from pathlib import Path
from itertools import combinations
from collections import Counter
exec(Path('coverage.py').read_text().split('hist=Counter')[0])
good=[]
for s,r in combinations([i for i in range(1,128) if i.bit_count()>=2],2):
 lc=(s|r).bit_count()-1 if s&r else s.bit_count()+r.bit_count()-2
 if lc>5:continue
 ok=[n for n in ng if (n>>13)&s and (n>>13)&r]
 bad=sum(1<<p for p in range(13) if not any(n>>p&1 for n in ok))
 if not bad:continue
 if any(not any(n&stars[i]&~bad and n&stars[j]&~bad for n in ok) for i,j in combinations(range(7),2)):continue
 good.append((s,r,lc,bad))
print(len(good));open('banks','w').write('\n'.join(' '.join(map(str,h)) for h in good)+'\n')
for bad in set(p for _,_,_,p in good):
 with open('neg.'+str(bad),'w') as f:
  print(*stars,file=f)
  for t,T in enumerate(stars):
   for a,b in combinations([i for i in range(13) if not T>>i&1],2):
    x=(1<<a)|(1<<b)|(1<<(13+t));bank={sum((bool(n&V&~bad)<<v) for v,V in enumerate(stars)) for n in ng if n&x==x}
    m=[v for v in bank if not any(v!=w and v&w==v for w in bank)];print(len(m),*m,file=f)
