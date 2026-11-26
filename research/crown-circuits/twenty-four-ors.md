# A 24-OR lower bound for the 12-crown at size 40

**Claim.** A monotone fan-in-two AND/OR circuit of at most 40 gates representing the 12-crown on the one-row, one-column promise requires at least 24 OR gates. The complete result is verified in Lean 4.36.0 by `crown_size_forty_requires_twenty_four_ors`. Its proof includes the threshold-two OR lower bound in the project’s circuit model. The companion theorem `crown_size_forty_at_most_sixteen_ands` gives the corresponding AND budget.

Write rᵢ and cᵢ for the two raw bits of label i. The output on {rᵢ,cⱼ} equals the indicator of i ≠ j. Every raw singleton is rejected by monotonicity and the matching false diagonal. No value on a same-side pair is prescribed.

## Reductions and diagonal facts

Choose a counterexample of minimum size among circuits of at most 40 gates and at most 23 ORs representing the crown. Remove dead gates. Invalid reads are false. Propagate constants by absorption or identity and bypass unary gates. Empty gates supply constants, and the promised function is nonconstant. Thus assume binary gates on valid earlier wires with no constants. If a gate computes the same function on the full raw cube as an earlier wire, redirect its uses and the output pointer to the earlier wire and delete it. By minimality all wire functions, including the raws, are distinct.

Use the previously kernel-checked bounds for this model. The circuit has exactly 23 ORs and at most 17 ANDs. Each diagonal activates at most two ORs. Call those activating two *saturated*. At most one unordered pair of distinct OR gates shares an input wire. If such a collision exists, at most five diagonals are saturated. The Lean declarations used here include `crown_size_forty_requires_twenty_three_ors`, `crown_trueOrFlags_le`, and `crown_collision_saturated_le_five`.

## Charging promised edges

For each raw singleton x, let tₓ count the ORs it activates. Monotonicity gives tₓ ≤ 2. Give x weight 2 to the power −tₓ, equivalently 4, 2 or 1 quarter-units.

Every wire accepts total singleton weight at most one. Start every weight at one and process gates chronologically, halving each singleton weight whenever that singleton activates an OR. A raw initially accepts only its own singleton. An AND has support contained in either parent. At a new OR every singleton in its support belongs to at least one parent and has just had its weight halved. Its new mass is at most half the sum of the parents’ old masses. Existing wire masses cannot increase. The final weights are the claimed ones.

The next step applies to any weights satisfying this wire mass bound. Charge each positive promised pair to the first wire accepting it and rejecting both singleton inputs. The output has this property. A raw cannot qualify, and a firing OR would have a qualifying predecessor. Thus this wire is an AND. Both parents accept the pair. As neither already qualified, each accepts at least one singleton, and since the AND rejects both singletons the parents accept opposite singletons. Distinct charged pairs give distinct ordered terms in the product of the two parents’ singleton masses, directing each endpoint to its accepting parent. Each AND pays at most one. Total demand is at most 17.

Write the row and column weights in quarter-units as 1+uᵢ and 1+vᵢ. Let e be the sum of the excesses across all 24 raws. Expanding the products over all 132 ordered off-diagonal pairs, and dropping the nonnegative quadratic terms, gives demand at least (132+11e)/16. Each raw occurs eleven times. Hence e ≥ 13 is impossible since 275 > 16·17.

If a collision exists, at least seven labels are nonsaturated. Both raws of each activate at most one OR, giving at least two quarter-units apiece. Then e ≥ 14, a contradiction. Now suppose no collision exists.

## A threshold restriction

The first OR firing on a raw singleton x reads x directly. A true predecessor expands backward through ANDs to raw leaves since no earlier OR fires. All leaves must be x. This predecessor computes x identically and therefore is the raw x by minimality.

If both raws of a label share their first OR, it reads precisely those two raws. Such gates are distinct for different labels. Let p count these labels. Identify rᵢ=cᵢ=zᵢ for every label. The resulting circuit computes threshold two on twelve bits: the zero and singleton inputs are rejected, and every input containing two distinct labels dominates a promised positive. Each shared-first OR now reads zᵢ twice, so bypassing all p leaves at most 23−p OR gates. Threshold two on twelve variables requires 2·12−4=20 OR gates in monotone binary circuits with unrestricted AND count and sharing. Hence p ≤ 3. [Ingo Wegener, The Complexity of Boolean Functions, §6.3, Theorem 3.1(ii), pp. 154–155](https://web.vu.lt/mif/s.jukna/boolean/blaues_book.pdf)

## Different first ORs

For each label let A and B be the chronological OR ID sets activated by its two raws. Their union has size at most two because both raw singletons are below their diagonal. Besides the p labels with a common first OR there are three cases.

- If at least one set is empty, the silent raw alone supplies three excess quarter-units.
- If the sets are nonempty and disjoint, both are singletons and supply two excess units together.
- If they overlap and their first elements differ, they are nested. Designate their raws a,b so that a activates g,h with g earlier than h, and b activates h alone. Initially the label supplies one excess unit.

In the nested case g reads a and h reads b directly. The other predecessor K of h is true on a. Trace K back through ANDs, stopping at raw wires or ORs. All leaves of this conjunction are true on a, so each leaf is a or g. Since g reads a, a implies g on every input. Thus K computes either a or g and by minimality is that wire. It cannot be a, since g and h would then share a predecessor. Therefore h = b OR g.

Call a nested label contaminated if g accepts a further raw singleton j other than a. This raw differs from b, whose first OR is h. On j, both g and h fire and no third OR can fire. Thus g is the first OR on j and reads j directly. It follows that g = a OR j and h = b OR g. The opposite raw j′ of label j is silent. Otherwise its first OR would have to be g or h to avoid a third active OR on that diagonal, but neither gate directly reads j′. This maps contaminated nested labels injectively into the labels with a silent raw: the image has a unique nonsilent raw j, whose ordered active pair fixes g,h, and the other raw input of g determines a.

For every uncontaminated nested label, simultaneously raise the weight of its earlier raw a from one to two quarter-units. No OR outside g,h is affected by this change for a. The singleton support of g is exactly {a}, and the singleton support of h is exactly {a,b}. These gates cannot be shared with a different adjusted label since their supports identify the label. Their new masses are two and four quarter-units respectively. Every other OR keeps its previous mass. Raw masses are at most one unit of full weight, and every AND support lies inside its parents’ supports. By chronological induction every wire therefore still has mass at most one, so the same AND charging bound applies.

Let n,d,z count the nested, disjoint and silent-orientation labels respectively; let k count the contaminated nested labels. We have k ≤ z and p+n+d+z=12. Shared-first labels have nonnegative excess. The adjusted total excess is at least

    2(n−k) + k + 2d + 3z = 2(n+d+z) + (z−k) ≥ 2(12−p) ≥ 18.

This exceeds the permitted excess, eliminating the zero-collision case. The conclusion is the 24-OR lower bound at size at most 40. A 40-gate circuit using 24 or more OR gates remains possible under this result.
