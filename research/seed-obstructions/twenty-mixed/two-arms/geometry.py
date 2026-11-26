from collections import Counter
from pathlib import Path
import sys
source=Path(sys.argv[1]).resolve()
sys.path.insert(0,str(source))
from verify_packing import samples
rows,front,target=samples(source/'L-meta-18968.json')
neg={(r&8191,(r>>13)&127) for i,r in enumerate(rows) if not target>>i&1}
pos={(r&8191,(r>>13)&127) for i,r in enumerate(rows) if (target^front)>>i&1}
stars=[sum({q for q,l in pos if l>>t&1}) for t in range(7)]
assert all(s.bit_count()==4 for s in stars)
hist=Counter()
for t,T in enumerate(stars):
    for u,U in enumerate(stars):
        if t==u:continue
        opposite=[j for j in range(13) if (U&~T)>>j&1]
        assert len(opposite)==3
        ordinary=[V for i,V in enumerate(stars) if i not in (t,u)]
        for p in range(13):
            if T>>p&1:continue
            candidates=[q for q,l in neg if (l>>t&1) and (q>>p&1) and all(q&V for V in ordinary)]
            number=sum(any(q>>marker&1 for q in candidates) for marker in opposite)
            assert number>=2
            hist[number]+=1
assert hist=={2:96,3:282}
print('Available opposite markers',dict(sorted(hist.items())))
