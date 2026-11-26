# Signed symmetry on semantic six-axis banks

A signed permutation sends a branch (j,b) to (P(j), b xor f_j). It preserves the activation tuple precisely when P-inverse applied to U_P(j) equals flip_f applied to U_j for all j. six_orbit.js checks this on the full 64-point truth table, pruning permutations by necessary activation sizes and directed influences |U_i XOR flip_j(U_i)|. Omitting a valid symmetry only increases enumeration.

One physical expression for each semantic state is chosen, transformed on its branch literals, and looked up by union. Two expressions agreeing on all words still agree after any signed coordinate permutation. The chosen necessary anchor class is also required to be invariant. Only a smallest representative is used for the anchor; successive helpers use the pointwise stabilizer of the anchor and earlier helpers. A lexicographically minimum sorted solution therefore has a surviving chain.

six_signed.js optionally requires that an anchor can share a disjoint packing with some member of each other mandatory class, allowing the anchor itself. Each candidate class must meet the unknown packing, making this necessary. Testing the post-filter symmetry over the earlier, larger class can only reduce the retained group. Neither backend imposes a chronology from the representative ordering.

sixexact.cpp rechecks each relaxed hit by building paid joins and enabling splits in an order-independent least fixed point. Each nonfull activation must be contained in a selected hot raw receiver. This is a separate full recheck of the profile.
