# Positive read-twice multilinear evaluation modulo powers of three

For a positive CNF of arbitrary width with each raw variable occurring at most twice, its canonical multilinear extension at arbitrary residues modulo 3^k can be evaluated deterministically in polynomial bit time for every fixed k≥1. The general polynomial exponent depends on k. One integer quadratic-sign contraction suffices for all precisions if every **failure** value is exactly 0, 1 or −1 in the working ring. In particular success 2 on every input meets this condition even modulo 9 and higher powers.

## Exact integer expansion

Let p_i be raw success and y_i=1−p_i be raw failure. Over the integers weight a Boolean assignment by the product of its p_i on ones and y_i on zeros. Summing over satisfying assignments gives the canonical multilinear polynomial, by agreement on the Boolean cube. Expand each clause indicator as one minus its failure indicator. If a bit s_c selects failure of clause c, every positive variable occurring in that clause must be zero. Summing each raw bit pays y_i if at least one of its clauses is selected, and one otherwise. An unused variable pays p_i+y_i=1. Within-clause repetitions can be removed after checking the raw bound. Repeated clauses may be retained as distinct indices. An empty clause gives zero, and an empty conjunction gives one.

Group variables by the same nonempty set A of incident clause indices, of size one or two. Write Y_A for the product of their failure residues. Let g_A(s) be one if some s_c with c in A equals one and zero otherwise. The exact expression modulo M=3^k is

    Σ_s (−1)^(Σ_c s_c) ∏_A [1−g_A(s)+g_A(s) Y_A].

The formula follows directly from the original assignment weights. In particular zero factors create no singularities.

For each A take b_A from {0,1,−1} congruent to Y_A modulo three and write Δ_A=Y_A−b_A modulo M. Discard zero discrepancies from the perturbation list. Each remaining discrepancy has cost v_A in {1,…,k−1}, its 3-adic valuation. Expand the product by choosing a subset S of discrepancies. Its coefficient is the product of their Δ_A. Its remaining factors are g_A for A in S and 1−g_A+b_A g_A elsewhere. Aggregate valuation at least k annihilates a term. This weighted truncation uses no division, even when a selected discrepancy has baseline zero.

For A outside S with b_A=0, pin every bit in A to zero. For b_A=1 the baseline factor is one. For b_A=−1 the factor is (−1)^g_A. For A in S use g_A=1−Z_A, where Z_A pins all bits in A to zero. Expanding these factors gives 2^|S| signed contractions. A chosen set of pins just takes their union. The sign exponent modulo two is the sum of the clause bits and all g_A with b_A=−1 outside S, with the pins imposed. A singleton OR is its bit. The OR of bits u,v is u+v+uv modulo two. Hence every contraction is an integer quadratic character sum on free bits. This proof keeps the full integer contraction before reducing it modulo M.

Write a quadratic exponent with a nonzero quadratic coefficient as uv+uL+vH+T, where L,H are affine in the other bits. Summing over u,v gives 2 times (−1)^(T+LH). Expand LH modulo two using w²=w. Iterate. When only an affine exponent remains, a nonconstant one sums to zero, and a constant gives its sign times the number of assignments. Isolated free bits are included. This yields a signed power of two or zero and determines the full residue even for k larger than the dimension.

## Cost and precision

Let t count nonzero discrepancies, and m count clauses after optional simplification. Define

    H_k = Σ_{S : Σ_{A in S} v_A < k} 2^|S|.

At most H_k contractions suffice. This is bounded by the sum of binomial(t,j)·2^j for 0≤j≤min(t,k−1), and by 3^t. Enumerate increasing lists of indices recursively, trying each later index once per visited subset and pruning before descent when valuation reaches k. This costs at most O((t+1) H_k) trials. Process the expansions of g_A one at a time with polynomial working space. Exact success pins p=0 or 1 may be propagated first by Boolean specialization. Combining parallel incidences can eliminate discrepancies or raise their valuation. The bound prices those gains on the actual grouped data.

Set D=2+L+k with L the input bit length, including indexed clauses and explicit coordinates. A conservative sequential multitape bound is O(D^8 H_k) bit operations and O(D^4) working bits. Schoolbook modular arithmetic uses O(D²) bit operations on O(D)-bit operands after coordinates are reduced. Building the O(m²) binary coefficient table including pins and doing O(m³) coefficient updates per contraction takes O(D^6) bit steps even if each lookup scans an O(D² log D)-bit indexed table. Rebuilding quadratic forms and coefficients, indexing subsets, enumerating pin masks, and reducing a signed power of two fit the stated slack. Arbitrarily long input coordinates can be reduced by streaming their bits. The k charge is explicit even if k is encoded in binary. Alternatively the original clause expansion takes 2^m poly(D) time, and the defining assignment sum takes 2^n poly(D) for n raw variables. H_k itself can be computed by multiplying the factors (1+2z^v_A) truncated below degree k and adding their coefficients. The precision bound makes no fixed-parameter claim in k.

At a common success point p=1/2 in the ring (the inverse of two exists), every assignment weighs 2^(−n), so multiplication by 2^n recovers the number of satisfying assignments modulo 3^k. If 3^k>2^n, this is the exact integer count. For graph edge-cover formulas take one positive clause per vertex and one variable per edge occurring in both endpoint clauses; their satisfying assignments are precisely edge covers. An algorithm polynomial in both length and k would therefore count all edge covers exactly in polynomial time.

## Where a naive lift fails

For the single clause (x), success p=5 modulo nine gives failure Y=−4 with baseline b=−1. The baseline answer is 1−b=2 and the true answer is 1−Y=5. The missing correction is −Δ=3. For p=4 the failure −3 has baseline zero; imposing its zero pin permanently would return one instead of four. Conversely, at p=2 the failure is exactly −1 and the clause-spin calculation is exact over the integers. The Boolean-assignment shortcut that weights both values by −1 at p=2 already fails modulo nine for (x): it gives −1 whereas the actual success weight is two. These sign conventions agree modulo three.
