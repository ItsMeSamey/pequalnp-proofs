# Five batches cannot cover ten marked H8 edges with two shared exceptions

Use the shared-exception domain of premises_6648_shared_projection_scope.md. H has eleven edges. Fix any set of ten marked edges. Every guarded H support is empty or a singleton: an anchor in H with two H leaves requires two distinct unmarked H edges, and each outside anchor (3,6,7) has at most one H neighbor. This includes the singletons allowed independently by the relaxation.

Thus the common exceptional supports E,F have size at most two each, except that the second may be F=E∪{t} of size three. Empty supports/clauses or absent exceptional supports cost nothing. Allocate each marked edge once to one accepting clean product.

Any clean product accepting at least two allocated edges needs a singleton clause. Otherwise its only nontrivial factors can be the two exceptional supports. A sole disjunction is singleton-positive. Two overlapping supports accept a singleton, and disjoint nonsingleton supports accepting a clean edge product would require a four-cycle: choose two distinct leaves from each. A nested pair also overlaps. These exhaust the no-singleton possibilities.

Let b be the singleton factor's vertex. Each accepted edge is incident to b; two distinct singleton clauses could give at most one edge. The remaining clauses which contain b impose no restriction on its mate. At least one clause must miss b to prevent accepting {b}; the permitted mate set is exactly the intersection of all selected clauses missing b. All such mates really are neighbors of b by cleanliness.

If |E|,|F|≤2, a batch accepting two marks must have its effective mate set equal to a complete two-element E or F. A given two-set determines at most one possible common neighbor b by four-cycle-freeness. Thus there are at most two distinct two-edge stars available as multiedge batches, even across different products. Exclusive allocation gives at most two surplus edges beyond one per batch.

In the remaining case E has size two and F=E∪{t} has size three. The mate set of a multiedge batch is exactly E or F. Every possible pivot neighbors both vertices of E and is thus the same vertex. All multiedge batches together can allocate at most the three edges from it into F, again giving at most two surplus edges above the number of batches.

Therefore five batches allocate at most seven edges for the fixed ten-mark mask, a contradiction. This is uniform in the choice of the unmarked edge. The resulting global conclusion is F(2,5)≤9. The local seven-edge capacity applies under the ten-mark mask; it does not assert F(2,5)≤7 on arbitrary masks.
