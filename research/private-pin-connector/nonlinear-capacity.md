# Information capacity of a fully open guarded interface

Let a bipartite graph have n_L and n_R open data bits on its shores and arbitrary interacting guarded private vertices. When selected, a private vertex requires even selected degree. Impose H_L x+H_R y=t over F2, with shore ranks h_L,h_R. Each shore has an arbitrary separate decoder of its open data, with disjoint raw-code fibers F_L(u), F_R(u). Suppose that every accepted assignment has a defined common decoded message u. The number M of attainable messages satisfies

    M ≤ 2^((h_L+h_R)/2).

This includes nonlinear, redundant, or partial codes. For partial codes the requirement that every accepted assignment decodes is essential.

For each attainable u, select a witness of minimum private weight for that message. Write a,b for the counts of its selected private vertices. Fix all right bits. Allow the a selected private left vertices and all n_L left data vertices to vary. Every private left vertex that remains selected is still eligible. The only other guard equations are the b selected right equations, which are linear on the left. The scores add at most h_L independent constraints. Therefore the affine space of such accepted assignments has dimension at least a+n_L−b−h_L. Its projection to raw left data is injective: a nonzero kernel direction with zero data change removes selected private vertices and still realizes u. With fixed right data the decoder forces every left assignment to lie in F_L(u). Thus |F_L(u)| ≥ 2^(a+n_L−b−h_L). Reversing shores and multiplying gives

    |F_L(u)| |F_R(u)| ≥ 2^(n_L+n_R−h_L−h_R).

Sum square roots over all M attainable u. The fibers on each shore are disjoint and lie in the raw Boolean cube. Cauchy–Schwarz therefore upper bounds this sum by 2^((n_L+n_R)/2), proving the claim.

With four unconstrained mixed rows the capacity is exactly sixteen messages (use four direct pairwise equality rows). With opposite pins and two additional rows the capacity is exactly eight (one private-pin six-cycle plus two direct equality rows). The all-guarded case lies outside this theorem. Requiring codeword validity externally can consume data guards or change which assignments are accepted; that is an additional interface restriction.

## Semi-open data

If g raw data vertices also impose guards, at most 2^((h_L+h_R+g)/2) messages are attainable. For the witness for u, let f_L,f_R count ineligible guarded data vertices and s_L,s_R selected guarded data vertices. Vary a selected private left vertices and all n_L−f_L eligible or open left data bits. The b+s_R selected right guards impose linear constraints. The fiber product is consequently at least 2^(n_L+n_R−h_L−h_R−z_u), where z_u=f_L+f_R+s_L+s_R. Since ineligible vertices cannot be selected, z_u≤g. Summation gives sum_u 2^(−z_u/2)≤2^((h_L+h_R)/2). For raw equality pairs with singleton fibers, every private-minimal witness must have all but at most h_L+h_R inactive data vertices guarded and ineligible.
