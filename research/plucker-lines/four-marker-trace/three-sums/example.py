from search import *
def parity(x):return x.bit_count()%2
def build():
    for n in [7,8,9]:
        for E in combinations(range(4,16),n):
            if not three(E):continue
            ass=assignments(E)
            for _ in range(80):
                a,b,S=profile(E,ass,2)
                if not all(len(S[i])==4 for i in range(4)):continue
                if not all(len(t)>=3 for t in S if t):continue
                if not any(len(t)==3 for t in S):continue
                for f,g in combinations(range(1,16),2):
                    seen={z+4*parity(m&f)+8*parity(m&g) for m,T in enumerate(S) for z in T}
                    if len(seen)==15:return E,a,b,S,f,g,seen
E,a,b,S,f,g,seen=build()
print(E,a,b,'high masks',f,g,'hole',set(range(16))-seen)
print([(i,sorted(t)) for i,t in enumerate(S) if t])
# Right ordinary copies share W (low two bits), private coordinates shift by two.
raw=list(E)+[(v&3)|((v&12)<<2) for v in E]
assert three(raw)
# The high code of the opposite side is exactly (f·(w,d|W), g·(w,d|W)).
# This can equivalently be expressed by ordinary primal and dual weights.
def rep(t):
    for k in range(1<<len(E)):
        w=0
        for i,v in enumerate(E):
            if k>>i&1:w^=v
        if w==t:return k
for m,t in enumerate(S):
    if not t:continue
    assert any(w==m for w,c,d in assignments(E))
print('raw is 3-connected',len(raw),'ordinary elements')
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from check_virtual_sums import models
aa=[4*parity(v&(f&3))+8*parity(v&(g&3)) for v in E]
l1,l2=rep(f>>2),rep(g>>2)
bb=[4*((l1>>i)&1)+8*((l2>>i)&1) for i in range(len(E))]
actual={z for c,d,z in models(raw,a+aa,b+bb,6)}
assert actual==seen
print('direct raw image verified; right primal/dual weights',aa,bb)
from itertools import product
period_cover=set()
for modes in planes():
    for h in range(1,4):
        pairs=[[z for z in S[m] if z<(z^h) and z^h in S[m]] for m in modes]
        for baselines in product(*pairs):
            if baselines[0]^baselines[1]^baselines[2]^baselines[3] not in [0,h]:continue
            for m,t in zip(modes,baselines):period_cover.update([(m,t),(m,t^h)])
assert period_cover=={(m,t) for m,T in enumerate(S) for t in T}
print('all',len(period_cover),'true cells covered by affine pairs on port planes')
