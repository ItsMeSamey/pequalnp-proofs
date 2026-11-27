from itertools import product
from pathlib import Path
rows=[]
for nq in range(1,5):
 q=sum(1<<(2*i) for i in range(nq))
 for same in range(nq+1):
  for opp in range(nq+1-same):
   for extra in range(5-nq):
    clean=sum(1<<(2*i) for i in range(same)) + sum(2<<(2*i) for i in range(same,same+opp)) + sum(1<<(2*i) for i in range(nq,nq+extra))
    for later in (0,1024,3072):
     w=clean|later
     if not w or later==3072 and opp:continue
     rows.append((w,q))
path=Path(__file__).with_name('t8-two-profiles.tsv')
rows.sort(key=lambda p:(min(p[0].bit_count(),p[1].bit_count()),p[0].bit_count()+p[1].bit_count(),p))
path.write_text(''.join(f'{w}\t{q}\n' for w,q in rows))
print(len(rows))
