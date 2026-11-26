"""Adjacent exceptional block with the other loose bit in the central child."""
from pathlib import Path
from itertools import combinations
from collections import Counter
import sys
proofbase=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[2]
sys.path.insert(0,str(proofbase))
from verify_mixed import coords,target
ng=[coords(i) for i in range(676) if not target>>i&1]
ss=[sum(1<<((6+j+d)%13) for d in (0,1,3,9)) for j in range(7)]
def inside(x):return [i for i in range(x.bit_length()) if x>>i&1]
def union(xs):
    ans=0
    for x in xs:ans|=x
    return ans
alln=(1<<len(ng))-1
points=[sum(1<<j for j,(p,l) in enumerate(ng) if p>>i&1) for i in range(13)]
lines=[sum(1<<j for j,(p,l) in enumerate(ng) if l>>i&1) for i in range(7)]
lc=[union(lines[j] for j in inside(m)) for m in range(128)]
pc=[union(points[j] for j in inside(m)) for m in range(8192)]
pairs=[[lines[t]&points[x] for x in inside(8191^ss[t])] for t in range(7)]
def failures(a,b):
    return [(t,u) for t,u in combinations(range(7),2)
            if not lc[a]&lc[b]&pc[ss[t]]&pc[ss[u]]]
def check(a,b,t,c):
    loose=[a,b]
    # D splits singleton raw children t,c. The loose bit r is in c's child.
    r=next(m for m in loose if m>>c&1 and not m>>t&1)
    sig=[tuple(bool(m&(1<<v)) for m in loose) for v in range(7)]
    env=[(lc[a] if x else alln)&(lc[b] if y else alln) for x,y in sig]
    safe=[sum(1<<i for i in inside(s) if points[i]&env[v]) for v,s in enumerate(ss)]
    hit=[pc[s] for s in safe]
    assert all(safe)
    assert all(any(points[p]&lc[a]&lc[b] for p in inside(z)) for z in safe)
    # On a c-positive, the c-side sets r=1. Comparisons into the opposite
    # child and ancestor AND siblings may ignore r because none contains it.
    env_c=lc[a if r==b else b]
    for j,k,env_k in [(t,c,env_c),(c,t,env[t])]:
        assert all(m&env_k&hit[k] for m in pairs[j])
    labels=[v for v in range(7) if v not in (t,c)]
    for j in labels:
        others=[v for v in labels if v!=j]
        w=[hit[v] for v in others]+[hit[t]|hit[c]]
        w += [hit[v]&(hit[t]|hit[c]) for v in others]
        w += [hit[v]&hit[k] for v,k in combinations(others,2) if sig[v]!=sig[k]]
        assert all(all(m&g for g in w) for m in pairs[j])
    ex=[(u^v).bit_count() for u,v in zip(ss,safe)]
    assert sum(ex)<=4 and sum(ex[j] for j in labels)<=1
    assert all(m&env[t]&hit[t] for m in pairs[c])
    arm,=set(inside(r))-{c}
    idle=set(range(7))-{arm,t,c}
    assert all(not ex[j] for j in idle)
    for j in idle:
        choices=[hit[i] for i in idle if i!=j]+[hit[t]|hit[arm]|hit[c]]
        assert all(m&g for m in pairs[j] for g in choices)
        # The four wholly external ordinary groups are pair-safe if both
        # loose leaves stay in the three-line block.
        for x,y in combinations(inside(8191^ss[j]),2):
            tri=[hit[u] for u in idle-{j}]+[hit[t]|hit[c]|hit[arm]]
            two=[hit[u] for u in (idle-{j})|{arm}]+[hit[t]|hit[c]]
            assert all(lines[j]&points[x]&points[y]&w for w in tri+two)
            assert all(lines[j]&points[x]&points[y]&pc[ss[u]]
                       for u in range(7) if u!=j)
    for j,k in ((arm,t),(t,arm),(c,t),(t,c)):
        assert all(m&pc[ss[k]] for m in pairs[j])
    for ec in range(1,12):
        for et in range(1,12):
            if ec>=3 or et>=4 or (et>=3 and ec>=2):
                assert sum(ex[j] for j in labels)+4-ec+min(ex[c],4-et)<=4
    for e in range(2,12):
        assert 7-e+min(6,2*e-3)<=8
if __name__=='__main__':
    n=k=0
    for a,b in combinations([x for x in range(128) if x.bit_count()==2],2):
        f=failures(a,b)
        if len(f)!=2:continue
        common=set(f[0])&set(f[1])
        if not common:continue
        c,=common;n+=1
        for edge in f:
            t,=set(edge)-common;check(a,b,t,c);k+=1
    print(n,'adjacent banks;',k,'oriented exceptional pair-blocks')
