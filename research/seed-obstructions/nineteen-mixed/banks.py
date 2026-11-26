from pathlib import Path
from itertools import permutations, combinations
from collections import Counter
import sys
src=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(src))
from verify_packing import samples
rs,front,target=samples(src/'L-meta-18968.json')
raw=lambda r: (r&8191,(r>>13)&127)
ps={raw(r) for i,r in enumerate(rs) if (target^front)>>i & 1}
ns={raw(r) for i,r in enumerate(rs) if not target>>i&1}
ns={r for r in ns if not any(r!=s and not(r[0]&~s[0] or r[1]&~s[1]) for s in ns)}
obligations={(l,k) for p,l in ps for n,k in ns if not p&~n}
stars=[sum(1<<((6+j+d)%13) for d in [0,1,3,9]) for j in range(7)]
inc=[sum(bool(t&(1<<i))<<j for j,t in enumerate(stars)) for i in range(13)]
def move(x,perm):
    return sum(1<<v for i,v in enumerate(perm) if x>>i&1)
group=[]
for lperm in permutations(range(7)):
    imgs=[move(t,lperm) for t in inc]
    if set(imgs)!=set(inc):continue
    perm=[inc.index(t) for t in imgs]
    if all({(move(p,perm),move(l,lperm)) for p,l in rows}==rows for rows in (ps,ns)):
        group.append(tuple(move(v,lperm) for v in range(128)))
assert len(group)==24
def rep(bank):return min(tuple(sorted(p[m] for m in bank)) for p in group)
def tally(families):
    families=list(families); a=Counter(c for c,b in families);b=Counter(c for c,b in {(c,rep(b)) for c,b in families})
    return sorted(a.items()),sorted(b.items())
S=[v for v in range(128) if v.bit_count()>=2]
print('L8',tally((v.bit_count()-1,[v]) for v in S))
print('L9 ordinary',tally(((a|b).bit_count()-1-int(not a&b),[a,b]) for a,b in combinations(S,2)))
raws=[1<<i for i in range(7)]
ex=[]
for t in raws:
 others=set(raws)-{t}
 for triple in combinations(others,3):
    bank=sorted(others|{t|y for y in triple})
    if all(any(l&w and not k&w for w in bank) for l,k in obligations):ex.append((3,bank))
print('L9 exceptional',tally(ex))
print('exceptional orbit reps',sorted({rep(bank) for _,bank in ex}))
# Two raw-singleton missing families cannot cover all true singletons by raw labels.
