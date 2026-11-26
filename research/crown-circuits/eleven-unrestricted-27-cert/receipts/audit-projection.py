"""Independent recursive observable-atom sampling of the physical T11 projection."""
from pathlib import Path
import gzip
import sys

def rows(path):
    op=gzip.open if str(path).endswith('.gz') else open
    with op(path,'rt') as stream:
        for line in stream:
            yield [int(x) for x in line.split()]

def measure(template):
    atoms=[0]
    for j in reversed(range(7)):
        left=1<<(2*j)
        right=left<<1
        after=[]
        for prefix in atoms:
            if j>=len(template) or prefix&template[j]:
                after += [prefix|left,prefix|right]
            else:
                after.append(prefix)
        atoms=after
    sign=[frozenset(i for i,a in enumerate(atoms) if a >> s & 1) for s in range(14)]
    smallest=min(map(len,sign))
    def disjoint(pool,k):
        if not k:
            return True
        while len(pool)>=k:
            head,*tail=pool
            if disjoint([s for s in tail if not s&head],k-1):
                return True
            pool=tail
        return False
    eligible=len(atoms)>=11 and smallest>=2 and not disjoint(sign,6)
    return len(atoms),smallest,int(eligible)

root=Path(sys.argv[1])
pairs=[('catalog-3.tsv','projection-3.tsv',1),('higher-4/higher-4.tsv.gz','higher-4/projection-4.tsv.gz',31),('six/catalog.tsv.gz','six/projection.tsv.gz',101)]
for catalog,proj,step in pairs:
    checked=0
    for a,b in zip(rows(root/catalog),rows(root/proj),strict=True):
        assert a[:2]==b[:2]
        if a[0]%step:continue
        pred=measure(a[3:])
        assert pred == tuple(b[2:]),(a,b,pred)
        checked+=1
    print(catalog,checked,'verified',flush=True)
