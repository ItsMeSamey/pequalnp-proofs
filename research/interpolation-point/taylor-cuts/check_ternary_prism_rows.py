"""Native-edge and private-frame checks on all palette placements."""
from itertools import combinations, permutations, product
from ternary_prism_rows import prism_certificates, prism_rows, lift_double_prism
from ternary_frame import color

placements=list(product(range(3),(1,2)))
patterns=list(permutations(range(3)))
frames=[{i:i for i in range(3)},{3+j:j for j in range(3)}]
possible=[(i,3+j) for i,j in product(range(3),repeat=2)]
triangles=list(combinations(range(3),2))+list(combinations(range(3,6),2))
checks=0
for mask in range(512):
    edges=[e for k,e in enumerate(possible) if mask >> k & 1]
    expected={(0,1,(p[1]-p[0])%3) for p in patterns if all((i,3+p[i]) in edges for i in range(3))}
    cert=prism_certificates(edges,frames)
    assert set(cert)==expected
    for (_,_,e),w in cert.items():
        assert all(edge in edges for edge in w)
        assert [u for u,v in w]==[0,1,2] and sorted(v for u,v in w)==[3,4,5]
        assert (w[1][1]-w[0][1])%3==e
    feasible=False
    for (a,sa),(b,sb) in product(placements,repeat=2):
        if all((a+sa*u-b-sb*(v-3))%3 for u,v in edges):
            feasible=True
            assert all(sa==e*sb%3 for i,j,e in expected)
        checks+=1
    status,word,_=color(6,triangles+edges,use_prism=True)
    assert (status=="SAT")==feasible and status!="UNKNOWN"
    if feasible:
        assert all(word[u]!=word[v] for u,v in triangles+edges)

double_cases=0
for first,second in product(patterns,repeat=2):
    for (a,sa),(b,sb) in product(placements,repeat=2):
        feasible={(c,sc) for c,sc in placements
                  if all((a+sa*i-c-sc*first[i])%3 for i in range(3))
                  and all((c+sc*i-b-sb*second[i])%3 for i in range(3))}
        result=lift_double_prism(a,sa,b,sb,first,second)
        assert result in feasible if feasible else result is None
        slope=(first[1]-first[0])*(second[1]-second[0])%3
        assert bool(feasible)==(sa==slope*sb%3)
        if first==second==(0,1,2) and sa==sb:
            assert len(feasible)==(2 if a==b else 1)
        double_cases+=1
left={i:i%3 for i in range(6)}
right={6+i:i%3 for i in range(6)}
edges=list(combinations(range(3),2))+list(combinations(range(6,9),2))
for start in (0,6):
    edges.extend((start+3+i,start+j) for i in range(3) for j in range(3) if i!=j)
edges.extend([(3,9),(4,11),(5,10)])
assert prism_rows(edges,[left,right])==((0,1,2),)
assert prism_rows(list(combinations(range(3),2)),[frames[0],{0:2,1:1,2:0}])==((0,1,2),)
print(checks,"single-link placements; 512 end-to-end decisions;",double_cases,"double-prism cases; overlap and duplicate sites passed")

from ternary_prism_rows import orientation_classes
for signs in product((1,2),repeat=3):
    rows=[(0,1,signs[0]),(1,2,signs[1]),(2,0,signs[2])]
    expected={w for w in product((1,2),repeat=3) if all(w[i]==e*w[j]%3 for i,j,e in rows)}
    classes=orientation_classes(3,rows)
    actual=set() if classes is None else {tuple(e*s%3 for r,e in classes) for s in (1,2)}
    assert actual==expected

# A cycle with one odd matching is rejected before rank-capped enumeration.
nframes=8
edges=[(3*k+i,3*k+j) for k in range(nframes) for i,j in combinations(range(3),2)]
for k in range(nframes):
    p=(0,2,1) if k==nframes-1 else (0,1,2)
    edges.extend((3*k+i,3*((k+1)%nframes)+p[i]) for i in range(3))
assert color(3*nframes,edges,cap=1,use_prism=False)[0]=="UNKNOWN"
assert color(3*nframes,edges,cap=1,use_prism=True)[0]=="UNSAT"
