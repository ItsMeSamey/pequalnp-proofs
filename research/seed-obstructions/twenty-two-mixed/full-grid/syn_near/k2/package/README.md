# Eleven point wires and eight line wires with two repeated reads

This conditional exclusion applies when the extra line mask has support S of size s in {2,3,4}, the remaining o=7−s ordinary private expressions are disjoint, and every special output has an envelope on the same b remaining point features. The private expressions cost at most 11−b−o gates to reconstruct. The original point-gate budget is 14−s.

For each special label j, use every raw negative with j active whose point coordinates meet every ordinary neighborhood. A passing trace on a special positive must be separated from each such negative by an envelope feature. Thus for each incident point and each maximal eligible negative point mask, at least one of the b features must contain the point and be disjoint from the negative mask.

The ordinary pair-safety charge and the seven-star charge bound the remaining slack by 3s−3−b. The SAT clauses implement those two necessary charge bounds and the common-negative obligations. The checked range of b starts at zero and ends at the smaller of 11−o and 3s−3. The permutation check certifies all 24 automorphisms against the raw samples before reducing line supports. The 12, 35 and 45 instances, respectively, all returned UNSAT.

Run from this directory with Python and python-sat installed. A conflict-limited solver can return UNKNOWN, which does not certify exclusion.

    python independent.py 0 6000 > replay.log
    diff -u elementary.log replay.log

The package checks the finite envelope obstruction. Applying it to a circuit requires the stated structural hypotheses.

For promotions leaving at least four ordinary labels, use the enlarged special set size r and the effective original support size s−δ, where δ is zero or one shared-private gate of reconstruction overhead. All 55 instances for r=2,3 are infeasible even at s−δ=1. The promoted checker uses hereditary projected charge bounds for unsaturated instances and the elementary charge alone at saturation. Run it with the following command.

    python promoted.py

## Width-independent extension for eight line wires and two repeated reads

Write P for the number of original point wires and g for the number of paid point gates. The mixed count is P+9. A line support of size s costs at least s−1 line gates, so P+g≤25−s at total size 33. Let E be the exceptional label set of size r, and let o=7−r. The conditional argument requires the following two properties.

- The o ordinary pair-safe outputs can be recovered from the original point circuit with at most P−b−o+δ additional binary point gates in total, with δ the reconstruction overhead.
- The same b original point features separate each incident exceptional singleton from each raw negative activating its label and meeting every ordinary neighborhood on the point side.

Adding the reconstruction gates and subtracting the ordinary charge 3o leaves slack at most 25−s+δ−4o−b, independent of P. With δ=0 and E the original support, elementary.log and width.log exclude every feasible b for s=2,3,4 (97 instances). For r=2,3, at effective cost s−δ≥1, promotion-replay.log and width.log exclude every feasible b (60 instances). No fixed-width coverage assumption is used in these claims. The promoted checker switches to elementary charge whenever the projected implementation would use the eleven-input saturation rule. The ten additional instances use elementary charge throughout.

    python width.py
