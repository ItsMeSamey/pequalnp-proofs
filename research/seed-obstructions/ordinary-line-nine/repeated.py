from noand import main
from edge import *
cc=Counter()
for s in (v for v in range(1,128) if v.bit_count()>=2):
    assert main(s,s)=='all'
    h=failures(s,s)
    if h:
        assert s.bit_count()==2 and analyze(s,s)[0]=='all'
    cc['repeated loose']+=1
    for l in range(7):
        if not s>>l&1:continue
        ords=set(range(7))-{l}
        assert not any(t in ords and u in ords for t,u in h)
        safe=[sum(1<<p for p in inside(ss[t]) if not s>>t&1 or points[p]&lc[s]) for t in range(7)]
        assert all(safe)
        hit=[pc[z] for z in safe]
        # One special guard in the 6-ordinary skeleton; companion w needed
        # only if T and w's bits admit it, and equal bits can coalesce.
        for t in ords:
            others=ords-{t}
            hh=[hit[v] for v in others]+[hit[v]&hit[w] for v,w in combinations(others,2) if bool(s>>v&1)!=bool(s>>w&1)]
            assert all(all(m&g for m in pairs[t]) for g in hh)
        assert all(all(m&hit[v] for m in pairs[l]) for v in ords)
        r=sum((ss[t]^safe[t]).bit_count() for t in ords)
        assert r<=s.bit_count()-1
        cc['repeated raw in loose']+=1
print(cc)
