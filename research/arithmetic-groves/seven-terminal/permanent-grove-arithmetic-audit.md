# Arithmetic and Boolean scope of the seven-terminal grove

Audited source permanent-to-grove.md at SHA
8de6e2d5a3518de6af0f605dc0c5729b6fd2be4289fea4fd33dddf4fc0ae6d0f.
The isolated z consumes one tree. The required pair a0,c0 consumes
two distinct others. Therefore detaching either of the two distinct
pendants is impossible. The remaining two pair tests put the far
chain endpoints into the prescribed trees. This identifies the exact
three-pair weighted polynomial after substituting pendant weights one.
No determinant oracle is needed for this equivalence.

For a numeric evaluation oracle, after physical edge substitutions
each tag has degree at most 2m, where m is the number of edges.
The coefficient [L^N M^N R^N] follows from a grid of (2m+1)^3
distinct integer triples over characteristic zero. At identity input
the coefficient is the nonzero integer c_N. Dividing the corresponding
coefficient at input X by the identity coefficient yields Per(X).
For zero-one X the tag grid produces polynomial-magnitude edge weights.
A forest sum is bounded in magnitude by 2^m times the product of the
largest absolute edge weights; its bit length and the rational
interpolation intermediates have polynomial bit length. For formal
circuits the coordinatewise truncation proof uses O((N+1)^6)
operations per multiplication over the polynomial coefficient field.
The primary November 24 theorem concerns formal arithmetic circuits,
arbitrary field constants and arbitrary intermediate degrees:
https://raw.githubusercontent.com/openai/math/main/preprints/Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026/build/intro.tex
This establishes the stated exact characteristic-zero consequence
given the reduction. No characteristic-two consequence follows.

For Boolean feasibility of three fixed pair separations, enumerate
partitions of the at most six pair endpoints among three named forest
components, respecting separations. For each empty block guess an
extra distinct representative physical vertex. Require every original
graph component to contain at least one named representative or
endpoint. Test for three vertex-disjoint connected branch sets
containing their prescribed terminal groups, using fixed rooted
graph-minor recognition. Any successful branch sets can be extended
to a spanning partition by attaching additional vertices within each
original component, then taking a tree in each block. Conversely a
valid forest gives branch sets. The same proof applies immediately
to a (3,3,1) terminal partition. Thus Boolean presence is polynomial
on arbitrary hosts even though the exact polynomial is arithmetically
hard. Neither claim settles dense binary graphic root-plane decision.
