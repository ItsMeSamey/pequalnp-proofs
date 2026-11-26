from pathlib import Path
from collections import Counter
F=(1<<64)-1
halves=[sum(1<<w for w in range(64) if (w>>j)&1) for j in range(6)]
kept={i:[] for i in range(5)}
counts=Counter()
for i,line in enumerate(open('six-canon.txt')):
    U=list(map(int,line.split()))
    branches=[u&h for j,u in enumerate(U) for h in (halves[j],F^halves[j])]
    atoms={sum(((b>>w)&1)<<j for j,b in enumerate(branches)):w for w in range(64)}
    reps=sum(1<<w for w in atoms.values())
    q=4-len(set(U)-set(branches)-{F})
    sparse=any(((F^u)&reps).bit_count()<=2 for u in U if u!=F)
    counts[q,sparse]+=1
    if not sparse:kept[q].append(f'{i} '+line)
for q,lines in kept.items():Path(f'six-hard-q{q}.txt').write_text(''.join(lines))
print(sorted(counts.items()))
