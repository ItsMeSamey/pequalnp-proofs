# Five necessary anchor cases for the projective plane of order five

The public matrix in L-meta-10007 has 775 nonincidences and 186 incidences. The question asks for an explicit cover of all nonincidences by at most 17 rectangles that avoid every incidence. The decision remains open.

A 17-cover must have total area at least 847, counting overlaps. After enlarging all rectangles to maximal legal rectangles, at least six have area at least 48 and one has area at least 52. A single projective relabeling and an optional duality of the whole cover can put that distinguished rectangle in one of the following forms. The other sixteen rectangles remain unrestricted.

| Rows | Columns | Row mask | Column mask |
|---:|---:|---:|---:|
| 4 | 13 | 29 | 170913825 |
| 5 | 11 | 103 | 563068940 |
| 6 | 9 | 119 | 546291716 |
| 6 | 10 | 1861 | 195823621 |
| 7 | 8 | 1869 | 187435009 |

The [projective-plane surplus theorem](official10007comb/design-excess.md) gives an independent area lower bound of 846 here. The [integer area bound and orbit proof](rectangle10007-independent/anchored-rank.md) strengthen that to 847 and establish the five anchors. The [fixed-core correction](official10007comb/overlap.md) gives a further necessary bound when particular boxes overlap.

## Verification

Run these checks from this directory with Python 3.

```sh
python3 rectangle10007-audit/five_anchor_audit.py
python3 rectangle10007-audit/rank.py
python3 official10007/reductions/anchor_controls.py
sha256sum -c SHA256SUMS
```

The anchor checker replays the existing 21-box control, verifies closure on the matrix and rejects an empty refutation tree at 17. An extra 5-by-10 representative serves as a checker control. The full enumeration sources and their outputs are included.

```sh
c++ -O2 -std=c++17 rectangle10007-audit/spectrum.cpp -o /tmp/pg5-spectrum
python3 -c 'import json; print(*json.load(open("official10007/reductions/rows.json")))' | /tmp/pg5-spectrum
python3 rectangle10007-independent/anchor_orbits.py
```

Compare the census with [spectrum.txt](rectangle10007-audit/spectrum.txt) and the collineation enumeration with [anchor-orbits.txt](rectangle10007-independent/anchor-orbits.txt).

## Scope of review

The uniform theorem and strict area-846 bound received independent mathematical source review. The area-847 inequality and the exclusion of maximum area 50 received independent exact-rational checks. Independent reviewers checked the projective-frame and fixed-line coverage, the use of a global duality and the five representative masks. The 17-cover question remains open in each of these arbitrary-rest search branches.

The matrix and prior control come from the [official L-meta-10011 Lean theorem](https://github.com/open-goat/pequalnp-proofs/blob/b104ff3988c176aae2db960c2a71ddf975ef047c/lean/PEqualNP/Outside/L_meta_10011.lean).
