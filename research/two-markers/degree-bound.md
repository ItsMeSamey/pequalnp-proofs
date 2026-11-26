# Two symmetric markers can require polynomial-calculus degree three

Over GF(2), give bit i the weight 2^i. Use nine guard equations x_i(Ax)_i=0, with symmetric A specified by its row masks in order starting at zero:

    [324, 10, 5, 258, 192, 96, 49, 272, 137]

Both parity markers, of masks 274 and 134, must be one. Of the 512 assignments, the guards admit 10 with marker values (0,0), 10 with (0,1), 8 with (1,0), and none with (1,1).

**Proposition.** This instance has polynomial-calculus refutation degree exactly three, both in squarefree form and in ordinary polynomial calculus with the Boolean axioms.

The [checker](check_degree.py) represents squarefree polynomials as vectors in the basis of monomials through the degree bound. It starts from the axiom span and closes under the following multiplication rules and addition. At degree two it permits *every* source in the current span whose product by x_j has squarefree degree at most two. These sources form the kernel of projection onto the quadratic monomials omitting x_j, because each offending monomial maps to a distinct cubic. Row reduction on the forbidden columns gives a kernel basis. The dimensions in successive rounds are 11, 33, 33. The constant one is absent from the closed space. Any ordinary degree-two proof projects into this space by squarefree reduction.

At degree three the checker only multiplies sources of degree at most two. The successive dimensions are 11, 86, 129, 130, 130, and the constant one belongs to the final space. Every source and every reduced product has an ordinary derivation through degree three, since a repeated variable can be reduced using a Boolean axiom multiplied by a monomial of degree at most one. Thus the upper bound also holds for ordinary polynomial calculus. The example gives a lower bound on the degree required for a general symmetric two-marker test. Completeness at degree three remains open.

Run `python -B check_degree.py` from this directory.
