from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from check_virtual_sums import models
from connected_hole import rank
from itertools import product
E=[4,5,6,7,8,9,10]; raw=E+[(v&3)|((v&12)<<2) for v in E]
A=[3,3,3,0,3,1,2]+[0,4,0,4,0,4,0]
B=[2,0,1,2,0,3,1]+[8,8,0,0,0,0,0]
table={}
for c,d,z in models(raw,A,B,6):table.setdefault(z,[]).append((c,d))
m=(1<<len(raw))-1
def allbits(bit,i):
    v=m
    for t in table[bit]:v&=t[i]
    return v
groups=[]
for q,r in product(table,repeat=2):
    S=allbits(q,0)&allbits(r,1)
    if not S:continue
    groups.append((S.bit_count(),q,r))
    for cq,dq in table[q]:
        for cr,dr in table[r]:
            ker=[v for j,v in enumerate(raw) if not ((dq|dr)>>j&1)]
            rankT=rank(ker)
            codim=1 if not dq or dq==dr else 2
            defect=rank(raw)-codim-rankT
            assert S.bit_count()<=4+defect
print('example',len(table),'scores, maximum same-type size',max(groups,default=(0,))[0],'irreducible elements',sum(bool(any(allbits(q,0)>>e&1 for q in table)) and bool(any(allbits(r,1)>>e&1 for r in table)) for e in range(len(raw))))
