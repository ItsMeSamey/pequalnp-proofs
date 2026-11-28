# Counting ordered-image models with affine matching demands

The [solver](ring_image_affine_demands.py), SHA-256 `2fb45cdc4ccfd21e9d18f8a9ad5a09a0bf278c3ad34e5c3aa29a744361916a86`, takes four ordered physical fields and inverts the [selector-free compiler](read-two-ring-image.md). Failed recovery yields `off_image`. On a recovered source it recognizes positive clauses and negative binary conflicts forming the named line graph of a simple planar bipartite root, with every vertex star present as a positive clause. Other recovered sources can return `unknown`. Exactness below concerns this recognized class with an uncapped solver.

Every source model is a perfect matching meeting all positive demands. Apply the [existing pruning](ring-image-planar-demands.md) first. For each demand contained in a star, delete the other incident edges at every common endpoint. Retain the vertex set, restrict remaining demands to surviving edges, and discard repeated sets and proper supersets. An empty demand or absence of a perfect matching gives count zero. The empty root contributes one empty assignment when it satisfies all clauses. Write m for the number of surviving named edges.

## Discovering the equations

On the surviving graph let x be the binary incidence vector of an actual perfect matching. For each remaining D, fit a single affine function f(x) to zero on matchings avoiding D and one on matchings meeting D. The first family consists of matchings after deleting D. The second is the union, over e in D, of the families forcing e. For each such branch delete the two endpoints, find the residual matching hull, and reinsert the forced coordinate and all fixed zeros in original edge order. Empty families give no equations. A branch with base b and direction basis V imposes f(b) equal to its label and the linear part zero on V. Solving these binary equations is necessary and sufficient for exact agreement on every matching. A matching and independent alternating-cycle toggles suffice for each hull. All branch discoveries take polynomial time, including all edge-pinned subproblems. [Classification proof](pm-demand-affine.md) · [Matching-hull proof](bipartite-perfect-matching-affine-hull.md)

For a fitted hit, require f(x)=1. Evaluate the resulting parity row on the direction basis of the common unconditioned hull and translate its right-hand side by its value at the base matching. Row reduction detects inconsistent targets, giving zero, or selects r independent original equations Ax=b. Every discarded equation then follows on the actual matching set. The exponent u counts precisely the surviving demands whose hit has no affine representative after the initial pruning.

## Exact count and witness

Fix one planar bipartite signing of the original root and fixed orders on both shores. All unweighted perfect-matching determinant terms have a common sign. Calibrate once by the unrestricted determinant. For deletion set J and edge mask w, let Z(J,w) be the determinant with J set to zero and signs flipped on w, multiplied by that common sign. Thus Z sums the character (−1)^(w·x) over the remaining matchings. A zero calibration certifies an empty matching family. Keeping the same matrix order and zeroing forbidden entries preserves the sign even for forced or deleted subinstances. Taking separate absolute values of character evaluations would lose cancellations. [Signing proof](ring-image-planar-demands.md) · [Signed oracle](planar_character_oracle.py)

Let D₁,…,Dᵤ be the nonaffine demands and R all current deletions, including the initial pruned edges. Exact integer counting gives

```
C(R) = 2^(−r) Σ_{s ∈ F₂^r} Σ_{S ⊆ [u]}
       (−1)^(s·b + |S|) Z(R ∪ ⋃_{i∈S} Dᵢ, Aᵀs).
```

For each matching, character orthogonality enforces Ax=b and inclusion–exclusion enforces every remaining hit. The numerator is therefore divisible by 2^r. Store the initial count. If positive, scan the m surviving edge names, permanently deleting an edge whenever the same formula still gives a positive count. Every edge kept was necessary when tested and remains necessary under subsequent deletions. The final edges themselves form a satisfying perfect matching. The solver checks its assignment against the original recovered clauses. For precision k and recovered arity a it returns the original count C and physical residue (−15)^(k−a−1) C modulo 3^k. The image construction ensures 0≤C≤2^a, hence any positive count yields a nonzero residue.

## Resource bound and scope

One calibration plus the initial count and at most m witness queries require at most **1+(1+m)2^(r+u)** determinant calls. The optional nonnegative cap charges actual determinant evaluations cumulatively, including calibration. Exhaustion returns unknown and the index of the next required call. Discovery and its polynomially many pinned matching subproblems use flow and binary linear algebra outside that cap. Fraction-free elimination with row swaps on the signed integer matrices uses polynomial bit time per determinant. Hadamard bounds every minor of order h by h^(h/2), and signed summation adds at most r+u bits beyond the term bounds. All masks are visited sequentially. Total bit time is 2^(r+u) poly(B) and space is polynomial in the explicit physical input length B, including recovery and residue arithmetic. At the separate signed-source entry point the polynomial factor includes the numerical declared arity, since the source graph explicitly allocates all variable names.

The [degree-three theta family](affine-hit-theta-matching.md) has 2^j−1 distinct remaining demands, r=j, u=0 and exactly two models. This compares the two call bounds on the same ordered images. The [source comparison](planar-affine-demand-prior.md) documents the matching-hull, prescribed-parity and signed Pfaffian precedents.
