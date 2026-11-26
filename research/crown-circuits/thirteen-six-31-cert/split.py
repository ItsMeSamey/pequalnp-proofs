from collections import Counter
from pathlib import Path
F=(1<<64)-1;half=[sum(1<<p for p in range(64) if p>>j&1) for j in range(6)]
files={q:open('q%d.tsv'%q,'w') for q in range(2,7)}
stat=Counter()
for s in Path('hard.tsv').read_text().splitlines():
    i,*u=map(int,s.split());b={m for j,w in enumerate(u) for m in (w&half[j], w&~half[j])}
    q=6-len(set(u)-b-{F}); files[q].write(s+'\n');stat[q]+=1
for f in files.values():f.close()
print(sorted(stat.items()))
