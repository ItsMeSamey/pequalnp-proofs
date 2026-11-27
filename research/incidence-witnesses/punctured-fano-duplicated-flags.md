# Duplicated flags at a minimum OR root

Let A,B be the actual flag sets accepted by its parents. They cover the 16 flags. Both are proper and nonempty, since otherwise a single parent solves the original promise. Both parents reject all original negatives. Write L(A) for the incident-site count minus one plus the interior-edge matching number from punctured-fano-root-interfaces.md. If s is the physical size and h counts gates in both parent cones, then s+h ≥ 1+L(A)+L(B). Dead gates can be discarded.

At each d=|A∩B| the exact minimum of that right-hand side is 18, 19, 20 for d=0,1,2, then 19+d for d=3 through 14. Thus a 20-gate circuit with d≥3 needs at least d−1 common physical gate ancestors. This bounds actual shared gates using duplicate positive flags. Those shared gates need not have distinct forks or identical consumers.

The checker check-fano-overlap-cost.py fixes the cardinality of B and takes subset-lattice minima over supersets of the complement of A; inclusion-exclusion fixes d. A second audit enumerated each proper A and each proper subset T of A, taking B=(complement A) union T, and reproduced every entry.
