"""Projection and physical relocation of the unique unowned fork. No circuit search."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import runpy
d=runpy.run_path(str(Path(__file__).with_name('check-fano-eighteen-deletions.py')))
M=d['rows']; E=d['edges']; req=d['requirements']; allbits=(1<<21)-1
for init in [0,1]:
    for hot in [63,63<<6]:
        counts=Counter()
        for om in combinations(range(21),init):
            kept=allbits^sum(1<<i for i in om)
            for s in range(1,4096):
                if s&hot:continue
                U=0
                for e in E:
                    if e&s:U|=e&hot
                forced=[n for i,n in enumerate(M) if kept>>i&1 and n&U]
                cert=sum(1<<i for i,n in enumerate(M) if kept>>i&1 and
                         any(not ((n&(hot|s))&~z) for z in forced))
                assert cert&~kept==0
                if all(w&cert for w in req): assert (allbits^cert).bit_count()<=4
                counts[s.bit_count(),cert.bit_count()>=19 or all(w&cert for w in req)]+=1
        print(init,hot,dict(sorted(counts.items())))
