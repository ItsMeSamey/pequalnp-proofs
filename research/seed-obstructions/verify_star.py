from itertools import combinations
from verify_mixed import coords, target
diff=(0,1,3,9)
for axis,own,opp in [(0,13,7),(1,7,13)]:
 for c in range(opp):
    t={p for p in range(own) if ((p-(6+c))%13 if axis==0 else (c-(6+p))%13) in diff}
    bad=[coords(i)[axis] for i in range(676) if not target>>i&1 and coords(i)[1-axis]>>c&1]
    for pair in combinations(set(range(own))-t,2):
        assert any(all(b>>v&1 for v in pair) for b in bad),(axis,c,pair)
print('Both star orientations reject all pairs exterior to the full incidence line.')
