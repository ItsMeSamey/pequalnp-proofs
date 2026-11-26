from collections import Counter
from pathlib import Path
from itertools import permutations
here=Path.cwd()
values=list(map(int,(here/'batchrows.txt').read_text().split()))
p,n,*rs=values
pos=set(rs[:p]); neg=set(rs[p:])
stars=[sum(1<<((6+j+d)%13) for d in (0,1,3,9)) for j in range(7)]
signs=[sum(bool(star>>q&1)<<i for i,star in enumerate(stars)) for q in range(13)]
assert len(set(signs))==13
def mb(v,perm):
    return sum(1<<w for j,w in enumerate(perm) if v>>j&1)
g=[]
for lines in permutations(range(7)):
    moved=[mb(v,lines) for v in signs]
    if set(moved)!=set(signs):continue
    points=[signs.index(v) for v in moved]
    pm=[0]*(1<<13)
    for v in range(1,1<<13):pm[v]=pm[v&(v-1)]|1<<points[(v&-v).bit_length()-1]
    lm=[mb(v,lines)<<13 for v in range(128)]
    if {pm[r&8191]|lm[r>>13] for r in pos}!=pos:continue
    if {pm[r&8191]|lm[r>>13] for r in neg}!=neg:continue
    g.append(pm)
print('group',len(g))
import sys
path=Path(sys.argv[1])
fs={tuple(map(int,z.split())) for z in path.read_text().splitlines()}
reps={}
for f in fs:
    rep=min(tuple(sorted(pm[m] for m in f)) for pm in g)
    reps.setdefault(rep,[]).append(f)
print(len(fs),len(reps),Counter(map(len,reps.values())))
out=Path(sys.argv[2])
out.write_text(''.join(' '.join(map(str,k))+'\n' for k in sorted(reps)))
