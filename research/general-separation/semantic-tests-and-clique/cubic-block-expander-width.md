# Sparse quadratic coupling can force exponential transfer width in every coordinate order

For t cubic blocks on q=3t input bits take a simple degree-D expander G on t vertices with Ω(t) distinct edges across every half-balanced cut. Explicit infinite bounded-degree families exist. Starting with a bounded-degree expanding multigraph, discard loops and merge parallel edges *before* forming the Boolean polynomial: no cut loses more than a factor D in its crossing count. [Gabber and Galil, explicit expanders](https://doi.org/10.1016/0022-0000(81)90040-4)

Compute over GF(2) the function

    f(a,b,c) = Σᵢ(aᵢbᵢcᵢ+bᵢ) + Σ_{ij∈E(G)} aᵢaⱼ.

Its supplied bounded-fanin circuit uses O(t) gates. Consider a pointwise linear transfer representation for its sign T=(−1)^f in any ordering of the 3t individual inputs. At a cut, width w means the sign can be expressed as a sum of w real products of a prefix function with a suffix function; any sequential real matrix-product computation with w intermediate coordinates gives such an expression. The same rank bound applies to deterministic read-once decision diagrams with w states.

Cut just after floor(t/2) of the a-bits have appeared. Pin every b,c bit to zero. Up to multiplication of each row and column by a sign, the restricted prefix-suffix matrix is (−1)^{uᵀAv}, where A is the binary adjacency across the induced a-partition. Its real rank is exactly 2^{rank_GF(2)(A)}: distinct row characters are orthogonal, and their labels form the image of the associated binary linear map.

The crossing bipartite graph has Ω(t) edges. It contains an induced matching of size Ω(t/D²): after choosing uv, remove all edges touching any neighbor of u or v, at most 2D² edges per step. The selected endpoints give an identity submatrix of A. Thus every variable order has a cut requiring 2^{Ω(t)} width, including every order that keeps the three coordinates of each cubic block together. This also rules out polynomial bond dimensions for a pointwise binary tree tensor representation on the input bits: a subcubic leaf tree has an edge separating between one third and two thirds of the a-leaves (weight only these leaves and use a centroid). The same argument applies using expansion on all such balanced cuts.

**Checks on the scope.** The exact unrestricted signed sum for this very family is computable in polynomial time. For fixed aᵢ, summing (−1)^{aᵢbᵢcᵢ+bᵢ} over bᵢ,cᵢ gives zero when aᵢ=0 and two when aᵢ=1. Only a=1^t survives, giving signed sum (−1)^{|E|}2^t and satisfying count (2^{3t}−(−1)^{|E|}2^t)/2. Thus a scalar counter that contracts or simplifies before producing a pointwise tensor escapes the width obstruction.

For any supplied independent block decomposition Σᵢaᵢbᵢcᵢ+Q with Q an arbitrary quadratic, fixing one coordinate per block leaves a quadratic on the remaining variables. Summing its exact Gauss values on 2^t branches gives a deterministic poly(q,size)2^t algorithm; an explicitly supplied invertible affine change to block coordinates preserves this clock after polynomial substitution. Recovering a hidden decomposition has a separate cost. The rank obstruction does not cover arbitrary changes of coordinates, circuit rewrites, or algorithms for only the final scalar count. [Quadratic Gauss elimination](original-dag-quadratic.md)
