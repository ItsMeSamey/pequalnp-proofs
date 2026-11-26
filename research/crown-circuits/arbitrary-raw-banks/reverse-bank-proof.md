# Transposing the paired OR bank

Start with twelve paired inputs, one OR gate for each pair. An OR-only DAG supplies both operands of each of a terminal AND comparisons. An OR tree combines their outputs. Output taps of the bank may repeat. A circuit of size at most 40 has g ≤ 29−2a bank gates.

Delete unused bank gates. Transpose the bank by placing a distinct source bit at each of its 2a taps. Traverse the bank backwards. At every vertex, union all messages from its outgoing gates and output taps. Send the result to its two predecessors if it is an OR. A vertex with f messages costs f−1 unions. Each of the twelve inputs is essential, so the total is at most (2g+2a)−(g+12) = g+2a−12 ≤ 17. Repeated output taps each contribute one message.

A label now has a mask recording its reachable comparison operands. It cannot contain both signs of a comparison, since the diagonal cell must be rejected. Each pair of labels must take opposite signs on some axis, since their joint input must be accepted. Thus the masks give twelve pairwise disjoint subcubes. All useful intermediate masks are subsets of terminal masks, and duplicate masks can be merged. No terminal is a proper subset of another. Each nonsingleton terminal therefore uses one paid gate of its own. At most one terminal is a singleton: two disjoint half cubes exhaust the cube. At most five other paid masks remain, or six when there is a singleton terminal. We call them helpers. Each nonsingleton mask is the union of two strict earlier masks. These may overlap.

## Enumeration

Choose a maximum-weight terminal as the anchor. Its weight w counts its fixed axes. Twelve disjoint labels force w≥4. With a singleton, eleven labels lie in the other half, so w≥5. An anchor of weight w needs at least w−1 union gates in its subgraph: a connected subgraph containing w literal sources and q fan-in-two gates has at least w+q−1 edges and at most 2q. At least w−2 helpers therefore lie strictly inside the anchor. In either case at most three helpers remain outside the anchor. We have w≤7 without a singleton, or w≤8 with one.

Fix the anchor signs and axes by permutation and sign flips. In the singleton case, fix the singleton to the first positive sign and the anchor to the first negative sign. Enumerate reachable inside helpers first, then outside helpers. Inside helpers never depend on outside helpers. Strict parents have smaller support, so nondecreasing cardinality is a topological order, with equal weights in either order.

The general checker compares inside incidence matrices up to row and column permutations. Rows correspond to helpers and columns to anchor axes. Equal-weight rows can be permuted and columns can be sorted; the singleton axis stays distinguished. An outside axis can be named in order of its first appearance and its first sign can be made positive. No previously fixed object uses that axis.

For each family, form all terminal unions conflicting with the fixed terminals and search for enough pairwise incompatible masks. If a candidate is a submask of another, substituting the larger mask shrinks its cube and preserves all disjointness. The enumerator allows a candidate to coincide with a helper and allows unused comparison inputs; either relaxation is safe for an exclusion. It bounds clique size by cube volumes and greedy independent-set coloring.

fivebank.py and fivebank_enum.cpp give separate SAT and explicit encodings for five comparisons. control.py reconstructs a cost-18 reverse circuit as a physical 41-gate circuit and verifies all 144 cells. general_bank.cpp takes the number of comparisons, anchor weight, singleton flag, and optional reverse budget.

## Saturation for an arbitrary number of axes

Mark the axes used by the anchor and by every helper. All other terminals must conflict with the anchor. A terminal cannot have two distinct unmarked literals: these would be its only two operands and would miss the anchor entirely. A helper operand only uses marked axes. Therefore all unmarked axes may be identified into one, preserving their polarities. Every preexisting conflict survives and no terminal develops an internal conflict. An outside helper can introduce at most two new axes because its operands are literals or previous helpers. For r outside helpers it suffices to have w+2r+1 axes, allowing unused axes. This gives the saturation widths recorded below.

| Anchor weight | No singleton: sufficient axes | With singleton: sufficient axes |
|---|---:|---:|
| 4 | 11 | — |
| 5 | 10 | 12 |
| 6 | 9 | 11 |
| 7 | 8 | 10 |
| 8 | — | 9 |

All eight saturation strata gave no packing at budget 17. The file saturation-17.out records the results from wide_bank.cpp. The 18-union control found by the same enumeration reconstructs as control-enum41.json and has been tested on all 144 cells. A different 18-union positive control with five active comparisons is control41.json.
