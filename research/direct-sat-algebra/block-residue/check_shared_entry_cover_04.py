"""Small 04 controls for minimum shared-entry covers; run only with scheduler approval."""
from itertools import combinations, product

from shared_entry_cover import minimum_cover, solve


def oracle_cover(edges):
    vertices = sorted({v for edge in edges for v in edge})
    for k in range(len(vertices)+1):
        for chosen in combinations(vertices,k):
            if all(set(chosen).intersection(edge) for edge in edges):
                return k


def check(n,gates,pins=(),clauses=(),equalities=(),output=None):
    def accepts(raw):
        w=list(raw)
        for a,b in gates:
            w.append(1-(w[a]&w[b]))
        return (all(w[v]==b for v,b in pins)
                and all(w[x]^w[y]==b for x,y,b in equalities)
                and all(any(w[abs(l)-1]==(l>0) for l in row) for row in clauses)
                and (output is None or bool(w[output])))
    expected = any(accepts(raw) for raw in product(range(2),repeat=n))
    status,cover,groups,raw=solve(n,gates,clauses=clauses,pins=pins,
                                   equalities=equalities,output=output)
    assert status==("sat" if expected else "unsat")
    assert (raw is not None and accepts(raw)) if expected else raw is None
    return cover


def main():
    all_pairs=list(combinations(range(4),2))
    for mask in range(1<<len(all_pairs)):
        edges=[e for i,e in enumerate(all_pairs) if mask>>i&1]
        result=minimum_cover(edges)
        assert len(result)==oracle_cover(edges)
        assert all(set(e).intersection(result) for e in edges)
    # Only h, z, w are observed. The hidden primary with ID zero wins the
    # singleton-cover tie; (h,z,w)=(1,0,1) requires the SECOND cover value.
    gates=[(1,0),(1,2)]
    assert check(2,gates,pins=[(1,1),(2,0),(3,1)])==(0,)
    assert check(2,gates,pins=[(1,1),(2,0),(3,0)])==(0,)
    # Pilot h is a computed wire shared by three separate bad cones.
    # All three private roots and outputs are visible through pins.
    gates=[(0,1),(5,2),(5,3),(5,4)]
    for a,b in product((0,1), repeat=2):
        pins=[(0,a),(1,b),(2,1),(3,1),(4,1),(6,1),(7,1),(8,1)]
        cover=check(5,gates,pins=pins)
        # Producer is also bad (both primary bits observed), hence one more
        # vertex is needed to cover its independent edge {0,1}.
        assert len(cover)==2 and 5 in cover
    # Signed aliases, constants, empty networks and contradictory exterior.
    check(2,[(0,0),(2,0),(1,3),(4,0)],equalities=[(0,2,1)],output=5)
    check(0,[],clauses=[()])
    print("64 minimum-cover graphs and 8 original NAND witness/UNSAT fixtures")


if __name__=="__main__":
    main()
