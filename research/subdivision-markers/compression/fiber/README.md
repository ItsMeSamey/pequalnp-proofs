# Exact affine-flat dimension for joint quadratic fibers with a shared interface

Work over the binary field. Each block i has private coordinates U_i and the same k public coordinates S. Its Boolean quadratic q_i may use all of U_i and S. Consider the simultaneous equalities q_i=b_i and fix any witness. Translate the witness to zero and subtract each constant, so each translated quadratic vanishes at zero. The largest dimension of a linear space of zeros in this translated system is precisely the largest dimension of an affine solution flat through the original witness.

## One quadratic and XOR

For a quadratic vanishing at zero on an n-dimensional W, let its polar rank be 2r and let its signed sum be J=sum_x (-1)^q(x). The largest totally singular dimension is

    w(q) = n-r-[J<=0].

When the radical has a nonzero linear restriction, J=0. A subspace projects to an isotropic subspace of the symplectic quotient (dimension at most r) and contains at most dim(radical)-1 radical directions. Equality follows by picking a Lagrangian, on which q is linear, and correcting each lift by a multiple of a radical vector of q-value one. When q vanishes on the radical, factor it out. Every singular nonzero vector v in the nondegenerate quotient splits off a hyperbolic plane: take w pairing one with v, and add v to w if necessary to make q(w)=0. Remove the plane by orthogonal complementation. Its signed sum is +2. A nondegenerate dimension-2r form has signed sum of magnitude 2^r by symplectic basis factorization, so whenever r>=2 it has a nonzero zero. At the last plane the positive sign gives a singular line and the negative sign gives none. This proves the formula, including the zero-dimensional case.

Every totally singular subspace T extends to one of dimension w(q). For any member v of T outside the radical, split off the hyperbolic plane as above, and replace the remaining T-basis elements by representatives in its orthogonal complement by adding v when needed. Both n and r decrease by two and one respectively, and J is divided by two, so w decreases by exactly one. Repeat. The remaining T lies in the singular radical, which may be included in any largest singular space. This proves extension without any regularity assumption.

Translating to a witness in an original b-fiber gives signed sum (-1)^b times the original global signed sum, independently of which witness was used. Orthogonal sums (XOR of private-variable quadratics) add polar ranks and multiply signed sums. In particular, a minority or unbiased fiber costs r+1 codimensions, and a majority fiber costs r.

## AND with shared observations

For H a subspace of S, restrict each block to W_i=U_i plus H. Call H feasible locally if some totally singular space projects onto H. Equivalently, take a basis h_j of H and seek one lift v_j=(u_j,h_j) per basis member subject to q_i(v_j)=0 for every j and B_i(v_j,v_l)=0 for j<l. The quadratic addition formula shows these constraints are necessary and sufficient. If feasible, extend the singular span of the lifts as above to a largest singular space in W_i. Its projection remains exactly H. Hence the largest local dimension with this projection is w(q_i restricted to W_i).

The exact global dimension through the supplied witness equals

    max over jointly feasible H of [sum_i w(q_i restricted to W_i) - (number of blocks - 1) dim H].

Indeed a global space projects to the same H in each block. It injects into the set of tuples of local projections with matching H-coordinate, of the displayed dimension or less. Conversely, choose a maximizing local space over H in each block and take all tuples with matching interface. That linear subspace is globally singular and attains the dimension claimed.

Enumerate H e.g. by reduced row-echelon matrices in 2^O(k²) time. The local lift equations consist of at most k(k+1)/2 quadratics in at most k dim(U_i) unknown bits. Count their joint zeros by expanding the equality indicator into the average of all signed sums of their binary linear combinations. Each summand is a quadratic sign sum computable by symplectic elimination, with polynomial integer bit lengths. This yields 2^O(k²) poly(input size) time, and a positive count recovers lifts by fixing their bits one at a time and recounting. Hyperbolic extension and elementary linear algebra construct the flat itself. The witness is an input to the flat algorithm.

## Disjoint quadratic predicates and multiplicative complexity

For k=0 the exact codimensions add, since every tuple of local zeros is an admissible witness. Write b_i for the desired outputs of s disjoint quadratic blocks having polar ranks 2r_i. The Boolean acceptance function is the AND of the s affine-shifted output bits. If every chosen fiber is nonempty and either minority or unbiased, this function has exact multiplicative complexity sum_i r_i+s-1 over binary XOR/AND with affine constants. For the upper bound each quadratic is an XOR of r_i products and an affine function by symplectic coordinates, followed by s-1 ANDs. Conversely, the guarded-affine chart theorem (or branching on one input of each AND through a fixed witness) supplies a through-witness accepting flat of codimension at most the number of ANDs plus one after pinning the output. The exact flat dimension forces the matching lower bound. Mixed choices of majority fibers give an exact flat profile but this reasoning does not always determine the gate count.

The local verification considers all 1,024 zero-constant quadratics in four variables, partitioned as two shared and two private variables. For every subspace of the interface it compares the maximal onto and unrestricted singular sizes whenever the former exists. A separate finite oracle checks the gluing dimension against direct global flat enumeration on 400 seeded systems with up to five total variables. Run python verify.py.
