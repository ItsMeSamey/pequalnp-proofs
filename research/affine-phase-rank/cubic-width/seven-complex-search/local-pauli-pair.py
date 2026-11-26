import sys
from collections import Counter
from itertools import combinations
from pathlib import Path
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'g3-complex-conic-search'))
from search import stabs
atoms=np.asarray(stabs());assert atoms.shape==(1080,8)
g=np.array([[1-2*((int((x^(p&7))==7)+((p>>3)&x).bit_count())%2) for p in range(64)] for x in range(8)])
r=((atoms==0).astype(int)-(atoms==2))@g
i=((atoms==3).astype(int)-(atoms==1))@g
zero=(r==0)&(i==0)
zero=zero[~zero[:,0]]
bad=[]
for p,q in combinations(range(1,64),2):
    if not (zero[:,p]&zero[:,q]&zero[:,p^q]).any():bad.append((p,q))
print('bad',len(bad),'of 1953')
print(Counter((len({0,p&7,q&7,(p^q)&7}).bit_length()-1,(((p&7)&(q>>3)).bit_count()+((q&7)&(p>>3)).bit_count())%2) for p,q in bad))
print('sample',bad[:10])
def predicted_bad(p,q):
    span={p,q,p^q}
    x={v&7 for v in span}
    return len(x)==2 and 0 in x and all((((v>>3)&v).bit_count()%2)==0 for v in span)
assert set(bad)=={(p,q) for p,q in combinations(range(1,64),2) if predicted_bad(p,q)}
