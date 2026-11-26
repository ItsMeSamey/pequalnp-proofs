# Lookup products sharing a primary address

Let m=2^t and let P be a power of two within a constant factor of m/t. A common primary index I selects a row in each of r banks. In bank a there are P independent t-bit pointer words and m independent payload bits, and the pointer in row π_a(I) selects one payload bit. Each π_a is a fixed known permutation. The target F is the AND of all r selected bits. Every input assignment is allowed. With identity permutations this is one explicit uniform circuit family of size O(rm): multiplex each pointer bit over the P rows and then multiplex the m payload bits. Fixed permutations merely rewire the rows; arbitrary nonuniform choices of the permutations yield the same size bound.

For W≥C rm, with C sufficiently large, the minimum number of size-at-most-W atoms in an exact real SUM for this function is
[
 \Theta(\max(1,rPm/W))\quad\text{for binary formulas},\qquad
 \Theta(\max(1,rP\sqrt m/W))\quad\text{for acyclic existential query programs}.
]
Formulas count leaves. The programs count query nodes, permit arbitrary successor lists and can be unambiguous in the upper bound. The constants are uniform in r.

For any particular pointer word in bank a, fix I to the index selecting that word, all other banks' payloads to all ones and all other pointers to constants. Varying the m payload bits in bank a now generates 2^m distinct functions on the target word. Write l_hi for source occurrences of the word in atom h, with i ranging over the rP bank–word pairs. Using [the ISA residual count](isa-sparse-range.md), zero-occurrence atoms together contribute just a scalar offset, and positive occurrences contribute O(l_hi) bits of residual information for formulas. For query programs they contribute at most min(m,O(l_hi²))≤O(l_hi sqrt(m)) bits. Thus for each pair the sum is at least m−1. The rP pointer words are disjoint, so summing their occurrence counts charges at most W to any atom. This gives both lower bounds.

Group the P possible values of I. In a formula for one group of g values, each bank uses a disjunction, over those i, of [I=i] and the bank's ordinary m-entry multiplexer on the pointer at π_a(i). Conjoin the r bank formulas. This costs O(rgm) leaves. Different groups are disjoint by their primary index. Use g of order min(P,W/(rm)), rounding within constants, to attain the formula bound.

For a query-program group each bank's [pooled lookup construction](isa-sparse-range.md) costs O(m+g sqrt(m)+g log P) nodes. Determine i from I in the group, query the high half of its π_a(i) pointer, pass through a matching payload node and verify the low half on the nondeterministically selected row, retesting the associated I at the end. Passing requires the correct row and unique payload address. Chain the r programs at their accepting exits. The number of accepting paths is a product of the per-bank path counts, each zero or one. The full group program costs O(r(m+g sqrt(m))). Take g of order min(P,W/(r sqrt(m))), reducing the absolute constant to leave room for the fixed O(rm) cost. Summing the disjoint group outputs gives the unrestricted target.

At a budget Θ(rmK) this has Θ(max(1,P/K)) formula terms and Θ(max(1,P/(K sqrt(m)))) program terms. Independent payloads and independent pointer words in all the banks do not cause multiplicative growth when the first address is shared. A product with independent primary indices lies outside this exact tradeoff.
