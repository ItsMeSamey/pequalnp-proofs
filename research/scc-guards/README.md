# Directed couplings between symmetric guard components

Given binary rows A, solve xᵢ(Ax)ᵢ=0 for all i and ℓ·x=1. Absorb a guard offset into Aᵢᵢ using xᵢ²=xᵢ. Draw an arc i→j for each off-diagonal nonzero. Assume every arc within a strongly connected component has its reverse. Component sizes and directed edges between components are unrestricted. The algorithm constructs in polynomial time a basis of actual guard models for the span of all models. Scanning the basis decides any odd linear marker and supplies a witness.

## Local span

In a connected symmetric component with diagonal indicator b, every model z obeys b·z=0 by summing the guard equations. Every unmarked vertex yields a feasible singleton. Join two marked vertices in an auxiliary graph whenever they admit a path with unmarked interior. This graph is connected if nonempty, by splitting ordinary paths at marks. A shortest allowed path between such a pair is induced, so its indicator is feasible. The endpoints have one selected neighbor each and the internal vertices have two. The singletons and path indicators generate the entire kernel of b. After canceling interiors, the endpoint pairs of a connected graph generate all even subsets of marked vertices by summing paths in a spanning tree. For b=0 the singletons suffice. Breadth-first searches from each marked root, stopping at other marked vertices, generate the required indicators.

## Directed composition

Add components in sink-first order. Let V be the span of models of the processed subsystem. Write D for the rows from the new component C into the old coordinates and b for its diagonal. Every old model s extends by zero on C. Its possible local extensions therefore contribute, in the total span, exactly the local model span at diagonal b+Ds supported on C alone, by subtracting the zero extension of s. The total span is the direct sum of V and the sum of these local spaces over all old models s.

If D annihilates V, the new local summand is ker(bᵀ). Otherwise an actual old basis model s has Ds≠0. The local spaces from contexts 0 and s already sum to the entire coordinate space on C. Their annihilators are the spans of two distinct binary vectors b and b+Ds, with zero intersection. This covers a zero vector in either context. Thus only two contexts need enumeration. Gaussian elimination keeps independent original models as witnesses. A marker hits some model precisely when it hits a basis model.

## Marker-dependent symmetric switch

On ℓ·x=1 the active ith guard is unchanged if uᵢ(ℓ·x+1) is added. The matrix becomes A+uℓᵀ+diag(u). Symmetric switching is possible exactly when A+Aᵀ=uℓᵀ+ℓuᵀ. For nonzero ℓ pick an anchor t with ℓₜ=1. Any solution may be shifted by ℓ to set uₜ=0, giving the unique candidate uᵢ=Aᵢₜ+Aₜᵢ. Check the candidate and, if successful, apply the preceding solver to the switched matrix. The switch preserves all witnesses with this marker. When neither criterion applies the implementation raises ValueError.

Run python check.py for exhaustive tests through three variables and seeded tests on larger component networks.
