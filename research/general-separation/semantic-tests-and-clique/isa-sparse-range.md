# Indirect storage access under signed sums and per-atom budgets

Let m=2^t and take P a power of two within a factor two of m/t. The input contains a log₂P-bit index I, P pointer words p_i of t bits, and m payload bits y. Output y at the address stored in p_I. Its n=Θ(m) bits support a uniform O(n)-size Boolean circuit: multiplex the P words one bit-position at a time, then multiplex the payload. Padding with unused bits can make the gate count at most the input length. This is the classical two-level indirect storage access function. Its disjoint blocks with 2^m subfunctions appear in Beame, Grosshans, McKenzie and Segoufin, Definition 2.2 and Lemma 2.5, following Paul. [BGMS](https://arxiv.org/pdf/1608.01932) [Paul](https://doi.org/10.1137/0206030)

Let W≥c log²m for a sufficiently large absolute c. Let S be the minimum number of size-W Boolean atoms in an exact real linear combination for the function, with W an upper bound per atom. Then

* For binary formulas counted by leaves, S = Θ(max(1,Pm/W)).
* For acyclic existential single-bit query programs counted by query nodes with unrestricted successor sets, S = Θ(max(1,Pm/(W sqrt(min(W,m))))).

The second upper bound uses unambiguous programs. All constants are absolute.

## A joint restriction count

Pin I=i and all pointer words other than p_i to zero. Varying only the m payload bits produces 2^m distinct Boolean functions of p_i. Let l_hi be the number of p_i occurrences in atom h, and d_h the number of distinct payload bits it reads. Then sum_i l_hi≤W and d_h≤min(W,m). Atom h has at most 2^(d_h) residuals as the payload varies.

In a formula with l=l_hi>0, take the fixed tree skeleton spanning all marked leaves. Outside subtrees evaluate to constants. Suppressing paths with a single marked child records a choice of four unary maps per path on a fixed binary skeleton of O(l) edges and vertices. The marked labels stay fixed. There are at most 2^{O(l)} residuals. In a query program keep the l named live query nodes. Propagation through fixed nodes gives the possible first live nodes or terminal outcomes from the start and from either answer at each live node. These incidences take O(l²) bits for l>0, regardless of the original successor lists. Acyclicity and existential path semantics make the contraction exact.

Atoms with l=0 contribute only one summed scalar offset. Given every residual of atoms with positive l, at most two offsets can produce Boolean-valued output, since its value at one chosen pointer word must be a bit. Thus m−1≤O(sum_h l_hi) for formulas. Summing over i gives P(m−1)≤O(SW). For query programs,
[
m-1\le \sum_{h:l_{hi}>0}\min(d_h,O(l_{hi}^2))\le O\left(\sum_h l_{hi}\sqrt{d_h}\right).
]
Summing over i yields P(m−1)≤O(S W sqrt(min(W,m))). The payload cap matters when W<m.

## Matching constructions

Partition the payload into aligned intervals of power-of-two length m', choosing the largest power of two ≤min(m,c₁W) for a sufficiently small constant c₁. Each interval is selected by fixed high pointer bits. For a formula and a single row i, test I=i, test these high bits of p_i, and read the selected payload value using a multiplexer formula on the remaining bits. Cost is O(m'+log m) leaves. Within one interval, take a disjunction over a group of g rows, where g is the smaller of P and a sufficiently small constant times W/(m'+log m), rounded down but at least one. Choose the constants so the atoms fit. The row and interval rectangles are disjoint on every assignment; their indicators sum to the function. This uses O(max(1,Pm/W)) terms.

For query programs use row groups of size g=min(P,floor(c₂W/sqrt(m'))), at least one, with c₂ sufficiently small. First check I and choose its row i in the group, rejecting if absent. Test on p_i the high bits selecting the interval and read the first half of its remaining address bits. From this prefix choose any matching address j in the interval, entering its shared query node y_j. If its value is one, choose a row i' in the group and enter the verification state for the remaining suffix of j at p_(i'). For each row, these states share a reverse trie: a matching bit advances to the remaining suffix and a mismatch rejects. Finally verify I=i'.

An accepting path forces i'=i, and both address halves agree with j. Thus there is at most one accepting path on any input. Removing the final index test can accept by using two different rows. The group dispatch and retests cost O(g log m) nodes by ordinary tries. Per-row high guards, forward prefix trees and suffix verification states together cost O(g(log m+sqrt(m'))). There are m' shared payload nodes. These costs fit within W since W≥c log²m and log m=O(sqrt(m')). The transitions may use many more arcs than nodes.

There are ceil(P/g) times m/m' rectangles. When m'<m one has W=O(m) and g=O(sqrt(m))<P eventually, so rounding does not introduce an extra factor. When m'=m there is just one column group. The resulting count is O(max(1,Pm/(W sqrt(min(W,m))))). The analogous ceilings for formulas follow identically, with group size of order W/m' before saturation.

At W=CnK(n) with fixed C≥1 and K(n)=ceil((loglog(n+16))^a), this gives Θ(n/(K(n)log n)) formula terms and Θ(sqrt(n)/(K(n)log n)) query-program terms. Thus explicit ordinary linear-size circuits give positive conditional-model simulation exponents independent of truth-table counting. The exponents are constants and do not show the unbounded slope in [the single-language transfer](nonuniform-simulation-exponents.md).

The checker isa_pooled_nbp_check.py tested 3,072 input and grouping cases, comparing the path count to the intended Boolean function and detecting inconsistent paths when the index retest is removed.
