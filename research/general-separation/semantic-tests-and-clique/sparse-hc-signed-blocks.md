# Deterministic subexponential exact Hamiltonian-cycle count for sparse digraphs

Let G be a directed graph with N≥1 vertices and m arcs, and set D=N+m. Two explicit binary quadratic systems give the exact directed Hamiltonian-cycle count by subtracting their integer numbers of solutions. Each has Θ(D) Boolean variables, O(D) equations, and O(log²(D+2)) monomials per equation. Consequently the October sparse-polynomial theorem gives deterministic time

\[
2^{O(D(\log\log D)^2/\sqrt{\log D})}
\]

and polynomial space for sufficiently large D. In particular the bound is subexponential in N whenever m=O(N). The graph may have arbitrarily ordered arcs and unbounded maximum degree. A cycle counts once up to cyclic rotation. In a multigraph, choices of parallel arcs are distinguished; collapse duplicates first for simple adjacency semantics.

## A signed sum with one contribution per Hamiltonian cover

Choose a Boolean selector x_e for each arc. At each vertex require exactly one chosen incoming and one chosen outgoing arc. A parsimonious quadratic encoding for any nonempty incidence list uses p_0=0 and equations p_i=p_{i−1}+x_i, p_{i−1}x_i=0, p_last=1 in the binary field. These equations forbid a second selection and require a first one. An empty list immediately gives count zero. This part uses O(D) coordinates and equations.

Choose one Boolean color y_v per vertex and fix y_root=0. Impose x_e(y_u+y_v)=0 for each arc e=(u,v) and define b_e=x_e y_u uniquely. Then the color is constant on every selected cycle. Let S be the vertices colored one. In a single common ordering of vertices, list all arcs first by tail and separately by head, breaking ties by arc identity. The b-selected subsequences encode the permutation on S induced by the cover, so its sign is (−1)^Q, where Q is the inversion parity between the two subsequences. The integer sign of this configuration is (−1)^{|S|+Q}=(−1)^{number of selected cycles in S}. If the cover has c cycles, its cut signs sum to (1−1)^{c−1}, with value one at c=1: the root cycle has fixed color and each other cycle independently contributes 1−1. Thus the sum over all covers and their rooted colorings is the desired count.

## A compressed quadratic encoding for inversion parity

Build a balanced binary tree with one leaf per arc. For each internal node let L and R denote its two child leaf sets. Every pair of distinct arcs splits at exactly one node. For a pair with one arc in each child, the indicator that its order differs between the two lists equals, modulo two, the sum of the two indicators that the R arc precedes the L arc. We may therefore compute Q by summing the parities of such ordered pairs at each node in each of the two restricted lists.

Put B=max(2,⌈log₂(D+2)⌉). Break each restricted list at a node into consecutive blocks of at most B arcs, restarting at that node and for each of the two orders. For a block W introduce an incoming prefix bit z (fixed to zero for the first) and outgoing prefix bit z′, shared with the next block, and one output bit w. Use the equations over the binary field

\[
 z'=z+\sum_{j\in W\cap R} b_j,\qquad
 w=z\sum_{i\in W\cap L} b_i+
 \sum_{\substack{i\in W\cap L,\ j\in W\cap R\\j\text{ precedes }i\text{ within }W}} b_j b_i .
\]

Writing each product with z as a list of monomials gives degree at most two and O(B²) terms. The equations determine all auxiliary bits uniquely. Summing w over the blocks counts each selected R-before-L pair in that node and order. The tree has O(m) internal nodes, and the sum of their list sizes is O(m log(m+1)). Including both orders, the sum of the ceilings of list size divided by B is O(m+m log(m+1)/B)=O(m). Thus no per-arc-per-level auxiliary bit is used.

The parity of all w and all y_v gives the sign bit ε=|S|+Q modulo two. Compute this last XOR with a binary tree of O(D) uniquely determined auxiliary bits. Produce one system fixing ε=0 and one fixing ε=1. Their ordinary integer solution counts differ by exactly the Hamiltonian count. If a witness is wanted, test deleting each arc in turn while preserving a positive count. A minimal positive subgraph consists of one cycle, and the polynomial number of self-reduction calls preserves the exponent.

## The exact theorem applied

The October manuscript's theorem titled *Counting common zeros of sparse polynomials* assumes a fixed degree k≥2 and a fixed integer c≥1. On V≥20 Boolean variables it permits at most cV explicitly listed polynomials, each having at most (log V)^c monomials of degree at most k, and returns the exact integer common-zero count deterministically in 2^{O_{k,c}(V(log log V)²/√log V)} bit operations and polynomial space. The hypotheses impose no individual variable occurrence bound. Here V=Θ(D), k=2 and one absolute c suffices for both bounds. Trivial small cases can be solved directly. This application uses the bound for sparse polynomial systems; the manuscript gives a different bound for constant-density fixed-width CNF. [October theorem and proof, TeX label thm:overview-sparse-polynomials](https://raw.githubusercontent.com/openai/math/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex)

**Check.** On 620 directed graphs, the checker compared every generated rooted cut's block parity with direct permutation inversion parity and compared each cover's signed sum with single-cycle recognition. It included every loop-allowed simple digraph through N=3 and 90 seeded graphs on four to six vertices with varying block sizes. It checks the reduction independently of the October counting algorithm. [Finite checker](./sparse_hc_signed_check.py)
