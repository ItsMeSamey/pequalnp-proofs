"""Replay the small mixed-cone searches on raw-row-preserving orbit representatives."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations
from pathlib import Path
import sys

here=Path(__file__).resolve().parent
root=here if (here/'verify_packing.py').exists() else here.parent/'synthesis_new/mixed'
sys.path.insert(0,str(root))
from verify_packing import samples

rows,front,target=samples(root/'L-meta-18968.json')
pos={r%2**20 for i,r in enumerate(rows) if (target^front)>>i&1}
neg={r%2**20 for i,r in enumerate(rows) if not target>>i&1}
neg={r for r in neg if all(r==s or r&~s for s in neg)}
assert len(pos)==28 and len(neg)==245
stars=[sum(1<<((6+j+d)%13) for d in (0,1,3,9)) for j in range(7)]
inc=[sum(bool(s>>p&1)<<j for j,s in enumerate(stars)) for p in range(13)]
assert len(set(inc))==13

def permute(mask,images):
    return sum(1<<z for i,z in enumerate(images) if mask>>i&1)

group=[]
for lines in permutations(range(7)):
    moved=[permute(i,lines) for i in inc]
    if set(moved)!=set(inc):
        continue
    points=[inc.index(i) for i in moved]
    pm=[0]*8192
    for v in range(1,8192):
        bit=v&-v
        pm[v]=pm[v^bit]|(1<<points[bit.bit_length()-1])
    lm=[permute(v,lines) for v in range(128)]
    def move(r):
        return pm[r&8191]|(lm[r>>13]<<13)
    if {move(r) for r in pos}==pos and {move(r) for r in neg}==neg:
        group.append((pm,lm))
assert len(group)==24

def extinct(family,extra,budget):
    length=16+(extra>=0)
    def project(r):
        bits=(r>>13)|sum(bool(r&m)<<(j+7) for j,m in enumerate(family))
        if extra>=0 and (r>>13)&extra:
            bits|=1<<16
        return bits
    ps=sorted({project(r) for r in pos})
    ns={project(r) for r in neg}
    ns=sorted(r for r in ns if all(r==s or r&~s for s in ns))
    n=len(ns)
    allneg=(1<<n)-1
    full=(1<<(len(ps)*n))-1
    @lru_cache(None)
    def separates(w):
        p,q,_=w
        return sum((allneg^q)<<(i*n) for i in range(len(ps)) if p>>i&1)
    def atom(j):
        return (sum(((r>>j)&1)<<i for i,r in enumerate(ps)),
                sum(((r>>j)&1)<<i for i,r in enumerate(ns)),int(7<=j<16))
    states={(tuple(sorted(atom(j) for j in range(length))),0)}
    for gate in range(1,length+budget):
        following=set()
        for state,spent in states:
            union=multiple=0
            for w in state:
                d=separates(w)
                multiple|=union&d
                union|=d
            assert union==full
            private=[separates(w)&~multiple for w in state]
            for i,j in combinations(range(len(state)),2):
                a,b=state[i],state[j]
                if a[2]==b[2]!=2:
                    continue
                for p,q in ((a[0]&b[0],a[1]&b[1]),(a[0]|b[0],a[1]|b[1])):
                    v=p,q,2
                    bad=~separates(v)
                    lost_a=bool(bad&private[i])
                    lost_b=bool(bad&private[j])
                    # Obligations originally covered by both parents remain
                    # covered after either operation. Only private pairs matter.
                    if spent+lost_a+lost_b>budget:
                        continue
                    new=[w for k,w in enumerate(state) if k!=i and k!=j]+[v]
                    if not lost_a and not lost_b:
                        following.add((tuple(sorted(new)),spent))
                    if spent<budget and not lost_a:
                        following.add((tuple(sorted(new+[b])),spent+1))
                    if spent<budget and not lost_b:
                        following.add((tuple(sorted(new+[a])),spent+1))
                    if spent+2<=budget:
                        following.add((tuple(sorted(new+[a,b])),spent+2))
        states=following
        if not states:
            return gate
    return 0

if __name__=='__main__':
    path=Path(sys.argv[1])
    records=[list(map(int,r.split())) for r in path.read_text().splitlines()]
    assert all(len(r)==10 for r in records)
    for name,limit,budget,extras,total,size in [
        ('16-P9L7',17,1,[-1],1041,65),
        ('17-P9L7',16,2,[-1],123,9),
        ('17-P9L8',15,1,[m for m in range(128) if m.bit_count()<=2],435,29),
        ('18-P9L7',15,3,[-1],15,2)]:
        if len(sys.argv)>2 and name!=sys.argv[2]:
            continue
        cases={(tuple(row[:9]),e) for row in records if row[9]<=limit for e in extras}
        reps={min((tuple(sorted(pm[m] for m in fam)),lm[e] if e>=0 else -1) for pm,lm in group) for fam,e in cases}
        assert len(cases)==total and len(reps)==size
        counts=Counter()
        for fam,e in sorted(reps):
            k=extinct(fam,e,budget)
            counts[k]+=1
        print(name,total,len(reps),dict(sorted(counts.items())),flush=True)
        assert 0 not in counts
