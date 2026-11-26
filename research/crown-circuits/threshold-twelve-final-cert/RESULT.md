# Exact size of twelve-input threshold two and of the twelve-label physical crown

The binary monotone threshold-two minimum is 29 gates, and the physical twelve-by-twelve crown minimum on its promised row-column inputs is 41. Both are finite circuit-complexity results. This is a mathematical proof with independently replayed finite searches. The complete result is not claimed to be a Lean theorem.

The grid construction and paired extension are verified by upper.py. For the lower bound, a size-28 candidate has at most eight AND gates by the twenty-OR lower bound. The zero-to-five AND cases and six-AND case were previously excluded. Raw normalization preserves the AND count at minimum size. The eight-AND argument is in eight-and-star.md. For seven ANDs, or-tight.md excludes branching size-two and size-three pure groups by specialization to ten and nine inputs. Pure groups cannot all be unshared: the first AND would have two small unshared pure operands. The group-size, star, and component restrictions in small-pure-groups.md and component-star.md imply the small graph census. The primary census is tightened.cpp. The independent assembly-review7c.cpp uses weaker tests and discharges its remaining graphs by quartet-cut.md. The longer final-quartet.md and triangle-doubleton.md give separate arguments for the original two remaining orbits. The seven-AND contradiction, together with the earlier exclusions, covers all AND counts. The crown lower bound follows from the prior unrestricted equivalence between a size-40 physical crown and a size-28 threshold circuit.

## Earlier research-fork dependencies

* Five-AND certificate: caefc483450d332277907c516806494863fc707f.
* Six-AND paired certificate: 57f67faef5cee635be5bfac0e9190368b5c3e143.
* Unrestricted pairing equivalence and ten-input lower bound 23: 6be4a5574d8ea16e42ce848f537ed10946901354.
* Eight-input size 19 and nine-input size 21: 2111f5f62b25a858972abddd75ee7d8f134eebd2.
* Eleven-input lower bound 26 uses the prior six-AND census and independent pure-group argument. It does not assume the twelve-input size or a ten-input lower bound of 24.

All the finite sizes above count binary AND and OR gates, with unrestricted fanout. The upper bound on the crown uses the prescribed one-row and one-column inputs. The stronger, separate result on ten-input size 24 is not a prerequisite.
