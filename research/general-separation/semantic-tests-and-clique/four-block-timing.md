# Borrowed-bit displacement at a fixed completion cutoff

Let N=2^n and d=4m. A deterministic controller sees the number of outputs already emitted and has exactly d borrowed bits and two clean bits initially 00. The output address is an external counter advanced only by emission. A tick can update all state bits and either emit one bit or remain silent. There is no extra clock or hidden state. Runs finish on the Nth emission, restoring the initial borrowed word. Distinct final states suffice for the counting lower bound. Displacement at time t is the Hamming distance of the borrowed word from its own initial value.

Split a seed into four m-bit blocks indexed cyclically from 0. Write B for the seeds with a unique minimum block weight attained at index 0. There is an explicit controller with O(d) bounded-fanin gates per tick emitting the zero table on every seed. Its total runtime is 13N on B and N elsewhere. Conversely, every deterministic controller in this model with distinct terminal states and runtime at least 8N on B has, for all sufficiently large m, at least a constant fraction of B reaching displacement Ω(√d) before tick 8N. This includes controllers with arbitrary nonuniform descriptions, regardless of the output bits or runtime outside B.

## Exact schedule

Let ρ rotate the blocks so that the minimum index advances by one. On clean value 0 and borrowed word b in B, silently enter (b,1). All other clean-zero seeds emit zero with no state change. From (ρ^i b,j), for b in B, 0≤i≤3, 1≤j≤3, use the following rule.

* If j<3, advance j by one silently.
* If j=3 and i<3, rotate once and set j to 1 silently.
* If j=3 and i=3, rotate once, set j to 0 and emit zero.

Define the transition arbitrarily on unreachable nonzero-clean tie states. The unique minimum index identifies i. Each orbit represented by b in B contains four distinct words and exactly one such b. Thus the twelve intermediate states at any address are disjoint across slow seeds and from every clean-zero state. The last rotation restores b. The same schedule repeats at every address, including the last. Counting four block populations costs O(d) gates: a balanced tree of binary additions costs O(m) per block since level j uses O(mj/2^j) gates. Comparisons, control and a bank of bit multiplexers for the cyclic rotation also fit O(d). No persistent workspace beyond d+2 bits is needed. The circuit family has an ordinary polynomial-time constructor in d+n.

For a global circuit or state budget δN/n with any fixed δ>0, choose d divisible by four, tending to infinity with d=o(N/n). Both the gate count and total persistent state then lie below δN/n eventually, even charging O(n) extra for the external address bookkeeping in the upper bound. The lower bound uses the stated separate-address model and exactly two clean bits. One possible choice is d=4 floor(N/(4n²)). The stream itself belongs to P and has a constant-output controller.

## Capacity and displacement

For each seed in B, take exactly its first T=8N pre-tick configurations, including the initial configuration and excluding the configuration after tick T. The address lies in {0,…,N−1} even if the run ends precisely on tick T. Two different seeds cannot share an address and full state at any of these times: determinism would give identical terminal states. A single run cannot repeat such a configuration before completion, since it would then loop forever. For B'⊆B whose borrowed words always remain within distance h of their own seeds at these pre-tick times, this gives

    8N |B'| ≤ 4N |B_h|,

where B_h is the radius-h Hamming neighborhood of the entire set B. Only the first T ticks were used; no assumptions on a later tail enter the count.

Write W_i for the four independent Bin(m,1/2) block weights under a uniform seed. Exchangeability and a union bound on six pairwise ties give Pr(B)=1/4−O(1/√m), since the largest binomial atom is O(1/√m). If a seed lies in B_h outside B, some j≠0 has W_0≥W_j and W_0−W_j≤h: flipping one bit can change this difference by at most one, and an endpoint in B has negative difference. Conditioning on W_j bounds the probability that W_0−W_j lies in [0,h] by O((h+1)/√m). Summing over three choices gives Pr(B_h)≤Pr(B)+O((h+1)/√m). For a sufficiently small absolute ε>0 and h=floor(ε√m), this is at most 3 Pr(B)/2 for large m. The capacity inequality yields |B'|≤3|B|/4. At least a quarter of the slow seeds therefore exceed this displacement before tick T. Equivalently the obstruction holds for excursion δ_d d whenever δ_d=o(1/√d); it does not establish a fixed-fraction displacement lower bound.

The separation concerns preserving a specified completion-time predicate with full terminal-state diversity. A controller charged only with printing the same table can emit zero immediately at each address.
