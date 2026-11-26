# Affine absorption within binary matroid separators

Represent the parity constraints as Mx=d and prescribe disjoint forbidden pairs of selected coordinates. Choose a binary decomposition tree of the coordinates, putting both endpoints of every pair in one leaf block. For a node S put U=span M_S, V=span M_complement. Its possible partial demands, before exclusions, form U∩(d+V), an affine coset of U∩V when nonempty. Enumerate its at most 2^b elements when the overlap dimension is at most b. Inconsistent global demands can be rejected first.

For every leaf S and partial demand s, solve M_S x=s by linear algebra. Write its pair violations as squarefree quadratics in free parameters. Row-reduce their quadratic coefficients while carrying the affine terms. Any remaining affine equations restrict the parameter space. Reject an inconsistent fiber, otherwise absorb the restrictions and repeat until no affine equation remains. For final independent quadratic equations q1,...,qr, the signed local count for a globally prescribed affine character is the sum, divided by 2^r, of the quadratic Walsh sums for all combinations of the equations plus the character exponent. Put the global constant in just one block. At internal nodes convolve the two child tables, keeping terms whose demands sum to the parent demand. Characters multiply on disjoint blocks, so this computes signed counts as well as ordinary counts. A constant number of specified characters changes the cost by that factor; the entire Fourier portfolio on k score bits costs an additional factor of 2^k by this direct implementation. With leaf ranks at most r the unsigned or single-character time is polynomial input size times (2^(b+r)+2^(2b)). This bound uses an input decomposition and locally contained pairs. Counts include cyclic joins. It is possible to extract a forest for existence by stripping cycles, but its character may then change.

## A planar graphic example with conditional affine cancellations

Take parameters h,u_i,v_i for i=1,...,m. The three pair products of module i are

    u_i v_i,   (u_i+h)v_i,   u_i(v_i+h+1).

Globally the three quadratic parts are independent for each i: after row operations their monomials are u_i v_i, h v_i, h u_i, distinct across modules. No affine constraint is exposed, so the final quadratic-row rank of this procedure is 3m. After fixing h in either fiber the quadratic-row rank before affine absorption is m. If h=0, adding the first and third equations gives u_i=0, eliminating all three. If h=1, adding the first and second gives v_i=0 with the same effect. Thus every conditioned fiber has final rank zero. These rank measurements concern the specified linear row reduction and affine absorption; other logical implications between the equations could also simplify them.

There are 2^(m+1) compatible assignments. For a character exponent c+a h+Σ(b_i u_i+e_i v_i) the signed total is

    (−1)^c 2^m ( [all e_i=0] + (−1)^a [all b_i=0] ).

In particular the character of h cancels globally despite the nonzero counts in both boundary states.

For a graphic realization use a plane multigraph with vertices O,H and U_i,V_i. Use two edges O–U_i, two O–V_i, one H–U_i, one H–V_i per module. Its planarity follows by drawing all length-two O–H paths in parallel and doubling their first edges. Take the plane dual as the join graph. Its binary cycle space equals the cut space of the potential graph. Fix the potential at O to zero and use h,u_i,v_i at H,U_i,V_i. To translate to an affine join space flip exactly the dual edges of H–V_i, and use the boundary of that fixed edge set as the demand. The six edge indicators in each module yield the six required factors, using each occurrence once. Splitting any nonempty proper union of modules from the others has one-dimensional matroid overlap: in the potential graph both connected parts share precisely O,H, so their graphic ranks sum to the total rank plus one; binary matroid duality preserves that overlap dimension. Equivalently the two partial potential assignments glue precisely when they agree on h. This example uses arbitrary demand and permits parallel edges; no all-odd-demand restriction is claimed.
