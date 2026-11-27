"""Count signed three-qubit stabilizer codes by wrong XZZ, ZXZ, ZZX incidences."""
import itertools

def parity(x):
    return x.bit_count() % 2

def comm(a,b):
    return parity((a>>3)&b)^parity((b>>3)&a)

groups = {frozenset([0]): ()}
for dim in range(3):
    for group, basis in list(groups.items()):
        if len(basis)!=dim:
            continue
        for p in range(1,64):
            if p in group or any(comm(p,q) for q in basis):
                continue
            groups.setdefault(group | {p^q for q in group}, basis+(p,))

profiles={}
census={i:{} for i in range(4)}
for basis in groups.values():
    for signs in itertools.product(range(2), repeat=len(basis)):
        # Representation i^phase X^x Z^z
        phases={0:0}
        for p,s in zip(basis,signs):
            for q,e in list(phases.items()):
                phases[p^q]=(e+((p>>3)&p).bit_count()+2*s+2*parity((q>>3)&p))%4
        profile=[]
        for k in range(3):
            zbits=7^(1<<k)
            local=[(p,e) for p,e in phases.items() if not (p&zbits or (p>>3)&(1<<k))]
            good=[]; bad=[]
            for y in range(8):
                on=int(all(2*parity(y & ((p&7)|(p>>3)))==e for p,e in local))
                (good if ((y>>k)&1)==((y&zbits)==zbits) else bad).append(on)
            profile.extend(good+bad)
        badsum=sum(sum(profile[8*k+4:8*k+8]) for k in range(3)); h=census[len(basis)]; h[badsum]=h.get(badsum,0)+1
        profiles.setdefault(tuple(profile),(basis,signs))
print({i: sorted(h.items()) for i,h in census.items()})
assert [min(census[d]) for d in range(4)] == [12,8,5,3]
assert [sum(census[d].values()) for d in range(4)] == [1,126,1260,1080]
