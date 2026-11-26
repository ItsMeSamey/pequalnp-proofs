# Weighted port flow through order 399

Use the producer components and OR-LCA lemma from README.md. Each original variable has just one owning component. No pair of adjacent ordinary variables belongs to the same component, so every graph neighbor of an ordinary local variable lies outside its component. Call a variable bad when it is the sole ordinary variable of a nonoutput component, and good otherwise. Let B,G be the counts, so B+G=2N and the B bad variables have distinct producer roots. Write e=s−2N+1 for the original circuit excess, t=e−B≥0, and δ=4N−1−s, so G=δ+t.

For a good variable x in a component with another ordinary variable, let b be its first ancestor in the local tree having a second local ordinary descendant. This ancestor is an OR by the LCA lemma. Choose a different ordinary descendant z in its sibling branch. There is an exterior neighbor y of z making (x,y) a nonedge: if x and z are on the same side choose a neighbor of z outside the star of x; otherwise y and x are on the same side, and choose y≠x. The unique x-to-b path must have an AND. Otherwise x alone forces b=1, so x+y would dominate the accepted z+y at b and all variables outside the b-subtree; both x and z influence the exterior only through b. This contradicts pair correctness. A singleton good variable whose component is the overall output also needs an AND on its path to the output, or x alone would be accepted. Choose one such private AND for each good variable.

At this AND, the sibling subtree away from x contains no local ordinary variable, by the OR-LCA lemma. Hence all its leaves are ports. On every incident pair x+y it must output one, because if zero it would annihilate the only possible influence from x and the circuit would give the same result as the rejected singleton y. Its entering ports are independent of all local variables, including x, so this sibling actually accepts all q+1 neighbor singletons. The private paths up to but excluding their first branching ancestor are disjoint across all good variables of either polarity. The chosen port-only sibling subtrees are pairwise disjoint as well: they leave these paths sideways into branches containing no local ordinary variable. They all lie in nonempty components.

Any producer with a local ordinary variable v can be active on at most one singleton, namely v. If a different singleton z activated it, choose an exterior neighbor y of v so that z+y is a nonedge, possible by the same common-neighbor and bipartition argument. Then z+y has exit one and dominates the accepted v+y on all its exterior variables, impossible. In particular a component with two or more local variables has empty singleton support.

Define k=q+1 and assign each wire weight min(k,number of all singleton assignments activating it). This is subadditive at any gate: the OR singleton support is a union and the AND singleton support is an intersection. Each selected sibling root has weight k. Each empty producer component's inputs consist only of ports, and their total weight is at least the exit weight. Add these inequalities over all chosen subtrees and all empty producer components. Their input port occurrences are disjoint. Each producer supplies its exit weight once per outgoing wire (the retained cut use and the other cut uses). After subtracting one exit weight per empty producer, we obtain

    kG ≤ sum over nonempty producers of fanout times weight
           + sum over empty producers of (fanout−1) times weight.

Nonempty producers have weight at most one and number at most 2N, since their local variable sets are nonempty and disjoint. Empty producer weights are at most k. If e0 is their total excess, then e0≤e−B=t, giving

    kG ≤ 2N+e+(k−1)e0 ≤ s+1+(k−1)t.

Substituting G=δ+t yields (q+2)δ≤4N−t≤4N. Consequently

    s ≥ 4N−1−floor(4N/(q+2)).

This establishes 100s≥Nq through order 399. At q=399 the bound is 636811 and the requested threshold is 636808. The proof uses specialization tests with at most two points and two lines at once for the OR-LCA step, and then singleton and pair tests. It does not use simultaneous negatives of full radius q.

The same flow counts an additional private sibling for each inactive bad owner v whose exit is zero on v. Its path to its component exit must have an AND, since an OR-only path would pass v as a singleton. Choosing one such sibling is disjoint from the good-variable choices and it accepts every neighbor singleton.
