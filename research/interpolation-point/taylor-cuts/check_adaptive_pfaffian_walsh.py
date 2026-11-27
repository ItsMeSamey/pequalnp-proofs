"""GF(2) sign spectrum and sector counts directly from K3,3 perfect matchings."""
from itertools import permutations, product
from collections import Counter


def parity(x):
    return x.bit_count()&1


def main():
    edges=[(a,b+3) for a in range(3) for b in range(3)]
    match=[sum(1<<(3*i+p[i]) for i in range(3)) for p in permutations(range(3))]
    def crossing(x):
        return sum(1 for i,(a,b) in enumerate(edges) if x>>i&1 for j,(c,d) in enumerate(edges[:i])
                   if x>>j&1 and (a<c<b<d or c<a<d<b))%2
    def verify(family):
        o=family[0]; basis=[]; coords={0:0}
        for m in family:
            z=m^o
            if z not in coords:
                bit=1<<len(basis);basis.append(z)
                coords.update({v^z:j|bit for v,j in coords.items()})
        size=len(coords)
        walsh=[sum((-1)**(crossing(o^v)^parity(i&j)) for v,j in coords.items())
               for i in range(size)]
        for seed in range(15):
            labels=[(seed*seed*(i+1)+(seed^i))%3 for i in range(9)]
            direct=Counter(); sectors=[0]*3
            for m in family:
                g=sum(x for i,x in enumerate(labels) if m>>i&1)%3
                direct[g]+=1
                for i,c in enumerate(walsh):
                    sectors[g]+=c*(-1)**(crossing(m)^parity(i&coords[m^o]))
            assert sectors==[size*direct[g] for g in range(3)]
        return sum(bool(c) for c in walsh)
    original=verify(match)
    for i in range(9):
        assert verify([m for m in match if m>>i & 1])<=original
        assert verify([m for m in match if not m>>i & 1])<=original
    print("K3,3 raw Walsh support",original,"and 285 whole/conditioned gain histograms passed")

if __name__=="__main__":
    main()
