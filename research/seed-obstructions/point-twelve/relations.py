from pathlib import Path
from verify_packing import samples
raw,front,target=samples(Path(__file__).parent/'L-meta-18968.json')
ps={r&((1<<20)-1) for i,r in enumerate(raw) if (target^front)>>i&1}
ns={r&((1<<20)-1) for i,r in enumerate(raw) if not target>>i&1}
allrows=sorted({(p&8191,n&8191) for p in ps for n in ns if not ((p&~n)>>13)})
constraints=[(p,n) for p,n in allrows if not any(q==p and x!=n and not n&~x for q,x in allrows)]
assert len(constraints)==1323
