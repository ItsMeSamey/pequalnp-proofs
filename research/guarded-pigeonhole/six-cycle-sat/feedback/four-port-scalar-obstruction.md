# A minimum-arity physical paired Pfaffian with no scalar principal matrix

Index four ternary gates by 0,1,2,3. The cyclic order of their visits in the all-off reference is

    0 2 3 1 2 0 3 1 2 3 0 1.

Use twelve distinct socket tracks, grouped by the three visits to each gate. Fixed feedback following the displayed word yields one all-off orbit. The two untied transpositions of a gate, in execution order, swap its first and third sockets, then its first and second. Taking both gives a genuine three-cycle. At the first socket the (first,third) chord endpoint precedes the (first,second) endpoint, so that the two paired chords nest. Distinct-gate chord crossings follow directly from alternation in the word. The table indexed by a switch mask is the Pfaffian of the principal section consisting of both chords of each switched-on gate. Its values in integer mask order from 0 through 15 are

    1 0 0 1 0 0 1 1 0 0 1 1 1 0 1 1.

Suppose a scalar matrix D over any field of characteristic two had these principal determinants. Its diagonal is zero. Its opposite-entry products at pairs 01,12,13,23 are one, and at 02,03 are zero. By diagonal conjugation arrange all six off-diagonal entries incident with vertex 1 to equal one. The three-coordinate principal minors containing 1 now determine D_ij+D_ji for every other pair: the sum is one in all three cases. Thus the ordered pairs at 02 and 03 are each (1,0) or (0,1), while at 23 the two entries are the two nontrivial cube roots of unity, in either order (if these roots are absent from the field the contradiction is immediate).

The 023 principal determinant is zero. Since both entries at 23 are nonzero, this forces 0 to be a source or a sink relative to both 2 and 3. In either case the four-coordinate determinant is 1+D_23+D_32=0: the double transposition (01)(23) contributes one and the two possible directed Hamilton cycles contribute D_23 and D_32. The table requires one. This excludes scalar realization even over the algebraic closure of F2.

Every nonzero binary table on at most three bits becomes a scalar principal-minor table over F4 after XOR normalization at a supported coefficient. For a normalized ternary table diagonal and pair entries specify the products D_ij D_ji. The final triple requires two oriented triangle products with prescribed sum and product equal to the product of all three pair values. If all three pair values are nonzero, solve the corresponding quadratic over F4; all opposite pairs can be normalized to products one. If some pair product is zero, a cyclic choice of forward nonzero entries can supply triangle sum one, or setting both entries of a zero pair to zero gives triangle sum zero. The zero table is handled separately. Hence four bits are the minimum for this obstruction. It concerns a single physical one-tour coefficient table, and does not obstruct the deterministic single-pencil universality test.
