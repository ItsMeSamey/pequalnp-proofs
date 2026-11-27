"""Two physical fixed-plane hosts indistinguishable by scalar queries on every radical block."""
from itertools import product
def span(vectors):
    S={0}
    for v in vectors:S.update({s^v for s in list(S)})
    return S
for positive in (False, True):
    # True dependency-code coefficients r1,r2,x0,y0,z1,z2,d*,r3 (binary order).
    cols=[1,17,5,85,9,41|(64 if positive else 0),2,34,128,160,
          4,8,28,36,72]
    D=[sum(((v&c).bit_count()%2)<<i for i,c in enumerate(cols)) for v in range(256)]
    assert len(set(D))==256
    odd=[D[v] for v in range(256) if v&64]
    matched=[v for v in range(256) if not v&64 and all(w&~D[v] for w in odd)]
    assert len(span(matched))==128  # L=D∩ker t, with t reading coefficient 64.
    R=span([1,2,128])
    # Ω reads coefficient pairs (x0,y0) and (z1,z2), hence its radical on L is R.
    assert len(R)==8
    witnesses=[(a,b) for a,b in product(R,repeat=2)
               if all(w&~(D[4|a]|D[8|b]) for w in odd)]
    assert bool(witnesses)==positive
    parts=[list(range(6)),[6,7],[8,9]]+[[i] for i in range(10,len(cols))]
    sets=[]
    for part in parts:
        values=set()
        for local in range(1<<len(part)):
            m=sum(((local>>j)&1)<<i for j,i in enumerate(part))
            if any((m&D[r]).bit_count()%2 for r in R):continue
            if any(not (m&(D[4|a]|D[8|b])) for a,b in product(R,repeat=2)):
                values.add(sum(((m&D[c]).bit_count()%2)<<j for j,c in enumerate((16,32,64))))
        sets.append(values)
    assert sets[0]==({0,1,5,6} if positive else {0,1,5,2})
    # Restricted to even masks (ker Q) on the six sites, the two tag
    # coordinates and two surviving output coordinates have full rank four.
    images=set()
    for m in range(1<<6):
        if not m.bit_count()%2:
            images.add(sum(((m&D[c]).bit_count()%2)<<j for j,c in enumerate((4,8,16,64))))
    assert len(images)==16
    assert sets[1:3]==[{0,2},{0,2}] and all(x=={0} for x in sets[3:])
    print('YES' if positive else 'NO','block signature sets',sets[:3],'physical lift count',len(witnesses))
