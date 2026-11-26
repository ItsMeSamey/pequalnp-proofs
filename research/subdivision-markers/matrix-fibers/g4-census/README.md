# Exhaustive determination of g(4)

Over F₂, the maximum dimension of an affine family of invertible 4×4 matrices on which inversion is affine is **four**. For any member X₀, normalization X → X₀⁻¹X preserves dimension and affinity of inversion since (X₀⁻¹X)⁻¹=X⁻¹X₀. It suffices to consider I+L with L linear. A four-dimensional example uses all matrices in L supported on rows 1 and 4 and columns 2 and 3. All products of two such matrices vanish, so (I+A)⁻¹=I+A.

**Upper-bound certificate.** Write φ(A)=(I+A)⁻¹+I when defined. Since φ(0)=0, affinity on L is equivalent to linearity on L. Each valid A satisfies A+φ(A)+Aφ(A)=0. For valid A,B the product (I+A+B)(I+φ(A)+φ(B)) equals I+Aφ(B)+Bφ(A). Thus A+B is valid with the required φ-value exactly when the cross term vanishes. Pairwise compatibility of a basis suffices: expansion at any binary subset sum has vanishing individual terms and vanishing pairwise cross terms. Necessity follows by restricting linearity to pairs.

Represent a matrix by a 16-bit integer in row-major order, with entry (1,1) least significant. The executable tabulates inverses by row elimination at all 65,536 matrices and verifies both inverse products. It computes conjugacy orbits using row-addition transvections; these generate GL₄(F₂) because elimination requires row additions and swaps, and each swap is three additions. Simultaneous conjugation preserves φ. Every nonzero space contains a nonzero valid point, which can be conjugated to its representative.

Fix a representative a and its highest set bit k. Choose coset representatives modulo the line spanned by a by clearing bit k. Eligible nonzero representatives form the initial sorted candidate list. Extend by appending candidates of strictly increasing highest set bit, retaining only those with zero in each previously appended pivot position. These are exactly the reduced echelon bases of quotient subspaces using the highest bit as pivot. The list is also filtered by compatibility with a and the current basis. Every canonical representative in a valid subspace belongs to that subspace, so these filters are complete.

| a | Orbit size | Initial quotient candidates |
|---:|---:|---:|
|2|105|95|
|19|1,120|5|
|20|1,260|7|
|72|210|47|
|310|2,880|0|
|311|2,880|0|
|314|3,360|1|
|315|2,520|3|
|4698|1,680|3|
|4699|1,344|0|
|4700|1,344|0|
|4701|1,344|5|
|4713|112|55|

The orbit sizes cover 20,159 nonzero valid points. The visit counts at dimensions 1,2,3,4 are respectively 13,221,88,4. Each count fixes a representative point, so these are marked representative cases. There is no fifth-dimensional space.

**Independent verification.** The Python implementation computes inverses from their permutations of all sixteen column vectors, conjugates by every invertible matrix to check the orbit partition, and stores each enumerated subspace as its complete point set. An extension verifies every new coset point's inverse, independently of the pairwise basis shortcut and echelon traversal. Weighting each marked count by orbit size and dividing by 2ᵈ−1 gives counts of all distinct normalized d-dimensional subspaces in the original coordinates.

Run the two checks from this directory:
```sh
g++ -std=c++17 -O3 g4.cpp -o /tmp/satbridge-g4
/tmp/satbridge-g4
python audit.py
```

The independent whole-space counts at dimensions one through four are **20,159; 21,035; 2,795; 35**. For dimension four, three marked spaces contain representative 2 and one contains representative 72. This gives (3·105+210)/15=35 after counting point-space incidences.

Both checks verify zero products in every maximal-dimension case. The C++ program tests all ordered basis pairs, and the Python program checks all 256 ordered pairs of points in each flagged representative space. Set U equal to the sum of the images of members of L. Their zero products imply U is contained in the common kernel. Then L embeds into Hom(F₂⁴/U,U), so 4≤(4−dim U)dim U. This forces dim U=2 and equality of spaces. Conversely every two-plane U defines an extremizer. There are (15·14)/(3·2)=35 choices.

The groups I+L for these 35 choices have order 16. All unnormalized extremal affine families are their left cosets. A coset determines its subgroup by left-translating back with the inverse of any member, so the total number of unnormalized extremizers is 35·20,160/16=44,100.
