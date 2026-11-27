# Recognizing bounded orientable genus with reversible port orders

Consider a connected closed network with m native switches and no isolated passive-only circle. A rotation system specifies at each gate the given alternating six-flag order or its reverse. Thickening and capping its facial walks gives a connected closed orientable surface. Every embedding in an orientable surface induces such a rotation system, whose capped genus is at most that of the original surface. Thus minimizing over rotation systems detects embeddability of genus at most g.

For a choice of reversals let s record which physical matching follows the left face when a wire is traversed in its direction. The other matching follows the right face. The in/out alternation guarantees that an entire left boundary can be followed in the forward direction, and an entire right boundary in reverse. In particular the two sets of faces have sizes c(s) and c(complement s), where c counts wire trajectories. Euler's formula therefore gives twice the genus as

    2+2m−c(s)−c(complement s).

In a connected network take the common untied-tour interlacement chart from [cycle-parity.md](../six-cycle-sat/feedback/cycle-parity.md). Each physical gate toggles two transpositions together, and the two indices of gate i belong to X according to their individual untied reference bits XOR s_i. The complementary routing uses precisely the complement of X. The circuit-nullity formula c(s)=1+nullity(A[X]) gives

    twice genus = rank A[X] + rank A[complement X].

Here A is a binary alternating matrix of order 2m. This is a joint test for the two physical complementary masks, not a separate minimum-orbit optimization on either mask.

To decide a given threshold enumerate disjoint nonsingular principal pivot sets I and J of total size at most 2g, including the empty sets. Require I on the first side and J on the second with unit clauses on the gate bits. Schur-complement the selected basis on its own side. Every nonzero Schur entry on a distinct pair of remaining indices forbids putting both indices on that side. These are 2-CNF clauses because every side-membership predicate is a single literal of a switch bit. Alternation guarantees zero diagonal, so there are no other residual entries to check. If the clauses are satisfiable the two ranks equal the two pivot sizes. Conversely an alternating matrix of rank r has a nonsingular principal restriction of size r: choose a coordinate basis modulo the radical of its bilinear form. Thus every low-genus rotation is tested for an appropriate pair of pivots. The complexity is (2m)^{2g+O(1)}; genus zero needs a single 2-SAT instance. Components can be separated and their minimum capped orientable genera added, since their ribbon neighborhoods are disjoint. Passive wire circles need zero genus.

[rotation_genus.py](rotation_genus.py) implements the decision and rotation witness for one connected native socket permutation, using rank on the pivot basis plus two indices to test Schur entries. Its deterministic replay compares every genus value per mask against direct facial walks and every tested optimum threshold against enumeration. The genus formula checks a supplied rotation in polynomial time even when g is unrestricted. Obtaining a positive-genus embedding does not extend the plane rooted-routing algorithm to that surface.
