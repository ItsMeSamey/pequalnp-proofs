from collections import Counter
from random import Random
from packet_layout import construct,preflight,SourcePlan
rng=Random(8411)
for r,a,m,delta,strict in [(2,1,128,4,True),(2,1,179,5,True),(2,2,4096,8,True),(64,2,123,8,False)]:
    net=[]
    for shore in (0,1):
        edges=list(range(m));rng.shuffle(edges); side=[(None,())]
        while edges:
            h=rng.randrange(1,delta+1)
            side.append((None,tuple(edges[-h:])));del edges[-h:]
        net.append(side)
    _,_,packets,shells=construct(net,m,r,a,a,delta,strict)
    assert sorted(e for q in packets for e in q if e is not None)==list(range(m))
    pairs=[]
    for i,sc in enumerate(shells):
        ls=[{e:label for (_,edges),label in zip(side,states) for e in edges} for side,states in zip(net,sc)]
        pairs.append(ls)
        for q in packets:
            ref=None
            for slot,e in enumerate(q):
                if e is None:continue
                p=(ls[0][e],ls[1][e])
                if slot>>i&1:p=p[::-1]
                if ref is None:ref=p
                assert p==ref and p[0]<=p[1]
        if strict:
            assert max(max(Counter(v.values()).values()) for v in ls)*r<=3*m
    D=r**(2*a)
    loads=Counter(tuple(ls[side][e] for ls in pairs for side in (0,1)) for e in range(m))
    assert D*sum(x*x for x in loads.values())-m*m<=2*m*delta*D
assert preflight(16,1,1)[2]==()
assert preflight(16,16,1) is None
print('4 layouts, including 3 with checked simultaneous source packing inequalities')
