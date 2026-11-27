# Branching on a gate with a private affine direction

Use the forward compiler state w with quadratic history equations P_j(w)=0 and next nonaffine product z=a(w)b(w). A downstream read has form ℓ(w)+cz plus later symbols. Include the output. Write a₀,b₀,ℓ₀ for linear parts. In either operand orientation and for α∈{0,1}, look for v satisfying

    a₀(v)=1, b₀(v)=0, ℓ₀(v)=αc for every downstream read,
    P_j(w+v)=P_j(w) identically for every prior equation.

This is a polynomial-time linear test. First intersect the kernels of all polar matrices. Within that common radical, each difference is constant and P_j(v)+P_j(0) is a linear functional obtained on a basis. [Forward state](forward-quadratic-shear-count.md)

Branch on b(w)=β. Both arms lose a dimension since b is nonconstant. Substitute z=βa. On β=α all future reads are invariant under translation by v. The constraints are invariant as well. Since a₀(v)=1 and b₀(v)=0, v is a nonzero direction within this slice. Parameterize it using v as one basis direction, remove that coordinate, and multiply the branch count by two. Thus the two child dimensions are n−2 and n−1 for a parent dimension n. Neither arm adds an equation. The rule permits symbols from earlier failed shears. Multiplication by two restores the count without doubling the work.

**Work for any supplied circuit.** Combine these splits with affine-gate substitution, successful shears, failed-shear coordinate introductions, and optional early termination. A leaf on n coordinates can enumerate its cube and evaluate the remaining DAG, checking history equations. Give the two children of a split probabilities 1/3 and 2/3 in order of increasing dimension, and unsplit steps probability one. If f and k are the respective counts of introduced coordinates and private-direction splits on a random root-to-leaf path, total deterministic work is at most

    poly(q+m) · 2^q · E[2^f (3/4)^k].

The child masses 2^{n−2} and 2^{n−1} sum to (3/4)2^n and distribute in the indicated proportions. A failed shear doubles the mass, a successful shear keeps it unchanged. Telescope on paths and sum over leaves. Further dimension drops or pruning only improve the bound. Depth is at most m gate-processing steps and each leaf contributes at least one to the bounding sum, so internal overhead is covered. No random estimation is involved. A sufficient condition for superpolynomial saving at polynomial m is k log₂(4/3)−f=ω(log q) on every path. It is open whether a strategy guarantees the required saving on all q log q gate DAGs.

**Arbitrary downstream core.** Suppose k primary bits x_i are read only through gates B_i(x_i,a_i(y)), where y denotes the q−k other bits, each a_i is affine in y, and each B_i is a nonlinear binary table. More generally suppose the calculation has form K(y,B_1,…,B_k) with arbitrary polynomial-size K. For fixed y each gate is constant in its private input at one control value and bijective at the other. Let p_i(y) indicate its bijective column, so p_i=a_i or its complement. Enumerate y and only 2^{wt(p(y))} attainable vectors of gate outputs, weighting each acceptance by 2^{k−wt(p(y))}. The number of core evaluations is exactly

    T=Σ_y 2^{wt(p(y))}=2^{q−k−r} Σ_{t in p(0)+image(p₀)} 2^{wt(t)},

where r=rank(p₀). Take r independent coordinates of p. Averaging 2 raised to minus the number of constant columns in that subset gives T≤2^q(3/4)^r. Equality holds for k=r. With k identical nonconstant controls the ratio T/2^q=(1+2^{-k})/2, so many nominal private gates need not generate a large saving. A deterministic black-box decision procedure for K needs all T attainable pairs on the false instance: a singleton accepting any missed attainable pair changes the answer. An explicit downstream circuit may allow further improvements.

**Graph-certified permutation.** If XOR gate g has inputs a primary x and a signal H omitting x, and every path from x to the output passes through g, then F(y,x)=K(y,x XOR H(y)). Redirect its consumers to x, including the output if needed, and delete dead logic. For each y the operation permutes the two x labels, preserving exact counts. Reachability and deletion are polynomial; repetition removes at least one gate per step. On the alternating register example the first remaining update has this form: its target is a primary after earlier rewrites, its control omits the target, and later reads use only the updated value. The earliest eligible rewrite removes this reversible region without supplied register labels, leaving the immutable quadratic readout times one free register. [Alternating example](mixed-shear-selector-count.md)
