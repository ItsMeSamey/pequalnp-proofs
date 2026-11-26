from pathlib import Path
import gzip
from collections import Counter
F=(1<<64)-1;H=[sum(1<<p for p in range(64) if (p>>j)&1) for j in range(6)]
groups={q:[] for q in range(1,6)};stats=Counter()
for i,line in enumerate(gzip.open(Path(__file__).resolve().parent/'ten-canon.txt.gz','rt')):
 u=list(map(int,line.split()));branches=[x&h for j,x in enumerate(u) for h in (H[j],H[j]^F)]
 atoms=[F]
 for b in branches:atoms=[c for a in atoms for c in (a&b,a&~b) if c]
 if len(atoms)<11:continue
 q=5-len(set(u)-set(branches)-{F})
 sparse=any(sum(not (a&v) for a in atoms)<=2 for v in set(u)-{F})
 stats[q,sparse]+=1
 if not sparse:groups[q].append(f'{i} '+line)
for q,rows in groups.items():Path(f'hard-{q}.txt').write_text(''.join(rows))
print(sorted(stats.items()))
