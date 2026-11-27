# Eleven mixed gates on cut 199

Use L={0,1,2,6,7} and R={3,4,5,8,9,10} in the issued eleven-vertex graph. For single-output binary monotone AND/OR circuits computing its full edge function, at least eleven gates must have syntactic raw ancestry on both sides. Arbitrary fanout and arbitrary local computation are allowed.

The 19 distinct rows and 17 columns require p,q≥5 distinct pure boundary wires. In a trimmed mixed cone, m≥p+q−1 by connectivity. With m≤10, either the mixed cone is a read-once tree with at most eleven leaves, or it has ten gates, exactly five pure ports on each side, and exactly one excess wire use when the output tap is counted. Count distinct syntactic boundary wires in the trimmed circuit, with repeated pins counted with multiplicity. The [explicit encoding](cut199-right-model.json) demonstrates that five right bits alone are feasible with unrestricted monotone decoding.

## Tree case

Use the monotone Karchmer–Wigderson relation on positive edges e and negative maximal independent sets I. A read-once formula on arbitrary monotone pure ports partitions the pairs into disjoint leaf rectangles: at an OR the player holding e chooses a true child, while at an AND the player holding I chooses a false child, using fixed tie-breaking. A leaf on side S cannot distinguish the pair when the support of e on S is contained in I. Color cells 1 at right leaves and 0 at left leaves. The resulting binary matrix is a sum over GF(2) of disjoint right-leaf rectangles, hence has rank at most the number of right leaves.

The [127-mask certificate](cut199-kw-short.cjs) uses seven positive and ten negative assignments. Among the 127 nonzero row masks, 21 pass the necessary parity test for being a row dependency: no column with all selected entries fixed has odd parity. No two distinct survivors have XOR also surviving. Consequently every binary completion has nullity at most one and rank at least six. Replacing its all-right edge 272 with the all-left edge 192 and complementing colors gives an all-one row; adding that row to each other row over GF(2) restores the same partial matrix. Thus at least six leaves on each side are required, excluding eleven leaves.

## One excess use

The [left encoder lemma](one-edge-cut-obstruction.md) pins the face on 0,1,2,6 when 7 is absent. With 0,1,2 present, varying 6,7 gives the four codes 7,15,23,31 up to a port permutation: the 7-only extension contains its four singleton units and cannot include the final unit because it rejects the empty right input.

On the right the empty assignment must have code zero: a nonzero lower bound leaves at most sixteen supersets for seventeen distinct profiles. In the local bit order 3,4,5,8,9,10, masks 1,3,5,7,11,17,19,33,41 all contain vertex 3 and have nine distinct left truth profiles. Thus singleton 3 has at most one code bit; it must have one since its profile differs from empty. Varying only left bits 6,7 and right bit 3 in the restriction above now varies exactly three decoder inputs. The target is majority on these three bits because they form a triangle, and there are no other active edges.

Propagate the other port constants and trim. The remaining three-input circuit has at most one excess use: deleting branches and contracting aliases into their source cannot increase graph cycle rank. For m' connected live binary gates on three distinct raw inputs that rank is m'−2, giving at most three gates. Monotone three-input majority needs four. For a direct proof, any first gate combines two inputs, say a,b, as AND or OR. If the two remaining gates use its result only once, the whole circuit is a formula with at most four leaves; two of the three variables occur once and cannot switch their lowest common ancestor between AND and OR as majority requires. If the first gate feeds both remaining gates, the final function absorbs one gate or becomes independent of the third input by idempotence and absorption. Hence this restriction also excludes one excess use.

The bound concerns mixed gates at this fixed cut. It does not settle the full 21- or 22-gate budget.

## Sharpness

Compute the two induced edge functions locally, then combine them in one mixed OR. For each of the five left vertices, form locally the OR of its right neighbors. AND each such result with its left vertex, using five mixed gates. Combine these five products and the local-function join with five further ORs. This gives exactly eleven mixed gates. The cut-specific mixed minimum is therefore exactly eleven. One direct realization uses 24 gates in total: one pure left gate, five right-neighbor ORs, seven gates for the induced right graph, and eleven mixed gates.

## A 22-gate realization and a separation for flat circuits

The witness in cut199-size22-mixed11.json computes the graph function on all 2,048 assignments with 11 right-local gates and 11 mixed gates. It contains nested ANDs. It attains the mixed lower bound within a total budget of 22. The absolute minimum total size remains open.

In contrast, any flat circuit with total size 22 needs at least 13 mixed gates on this cut. By the equality cases in star-family-bound.md, its 16 edges partition into seven nonempty stars with distinct centers. Each star with neighbors on both sides needs at least one mixed operand OR. Its product is mixed precisely when an opposite-side neighbor occurs. With b mixed products and d distinct sides represented by pure products, the collector needs at least b+d−1 mixed gates: contracting the pure collector components leaves at least b+d distinct inputs to the connected mixed collector. Grouping each side's pure products first attains this bound, and grouping same-side leaves first attains the operand bound. The enumeration in cut199-flat-count.py assigns each edge to either endpoint, retaining exactly seven centers. The 1,488 retained orientations have respective mixed minima 13,14,15,16,17,18,19 with counts 20,12,252,136,652,388,28. This separation concerns the ordinary graph function and cut; it supplies neither an 18272 witness nor a 4186 counterexample.
