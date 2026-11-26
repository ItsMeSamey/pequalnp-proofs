# Substitution audit and height-independent polynomial calculus composition

Use ordinary binary polynomial calculus (PC), with Boolean axioms x_v²+x_v, and degrees measured before taking Boolean remainders. In a substitution tree let Y_B=sum_(v in B)x_v, and let H_B be the common exterior read on node B, with H_root=0. For a child C of B this gives H_C=H_B+t_C, where t_C is the row of the local quotient applied to the child parity vector. All these are linear forms in the original variables.

The all-marked disjunction holds for arbitrary loopless directed inner and outer graphs. In a global odd witness, a child of odd parity and exterior field zero already contains an odd witness of its own. Otherwise the odd-parity children satisfy the quotient's odd-outdegree requirement and their number is odd. An isolated inner witness extends by zero; a quotient witness lifts by taking one representative in each selected block. No internal symmetry is needed.

## No proof-degree growth with substitution height

On a NO instance every quotient is NO as well: a witness in any quotient lifts through representatives and zeroes outside its node. Suppose each internal quotient Q_B has a PC refutation of local degree d_B with its usual odd marker 1+sum y_C=0. Derive the following standalone summary for every non-root node, working bottom-up:

    G_B=Y_B(1+H_B)=0.

For a leaf this is the original guard. At a non-leaf, substitute the linear forms Y_C in the local quotient proof and multiply its lines by G_B. The final line 1 gives the desired G_B. To initiate this simulation:

- Local guard Y_C(1+t_C) differs from the already derived child summary G_C by Y_C H_B. Multiplying the latter discrepancy by G_B gives Y_B Y_C(H_B+H_B²), which follows at degree four from the Boolean axioms. The product G_B G_C is obtained by multiplying the *previously derived degree-two row* G_C by the two affine factors of G_B. The proof of G_C itself is never multiplied.
- The odd marker times G_B is (1+H_B)(Y_B+Y_B²), a degree-three Boolean consequence.
- For a substituted Boolean axiom Y_C²+Y_C, use the sum of its constituents' Boolean axioms. Multiplication by G_B costs at most degree four.

Simulate addition by addition; simulate multiplication by a quotient variable by multiplying by the corresponding linear form, using individual-variable multiplications and addition. The degree is at most d_B+2. The certificate does not require Boolean reduction of intermediate formal polynomials. At the root, substitute its local refutation without multiplying its lines: its child guards are precisely the already derived summaries, and its odd marker is the original global odd marker. Thus the overall bound is

    max(4, d_root, max_(B internal non-root)(d_B+2)).

This bound concerns a supplied tree with previously sited quotient proofs. It remains valid at unbounded height. In particular one must distinguish multiplying a derived degree-two line from multiplying all the lines that derived it.

## Arbitrary labels and offsets

Suppose the hidden part of a nonempty module is visible to the outside only by its parity. Write A for the subset of {0,1} consisting of the exterior-field values h at which the internal system admits odd parity. Even parity is always attainable by the empty assignment. At least one h is in A because the singleton at v works when h equals its effective offset p_v (after self-coefficient absorption). Hence replace the entire module by a free parity bit if A has both elements, or by a bit whose one-setting requires h to be the unique element of A otherwise. This exactly preserves all projected assignments; one stored odd witness for each admitted field lifts the bit. Exterior constraints can be arbitrary predicates of outside variables and this bit. For uniform internal offsets p the set A contains p, and evaluating at the other field is exactly the all-marked odd-internal-degree question.

A larger simple interface is possible if internal off-diagonal entries are symmetric. Split the module into the two classes of effective offsets d=0,1. Let s_d be the parity of the selected members of that class. For common exterior field h, summing the vertex guards cancels every internal quadratic term in characteristic two. It leaves (0+h)s_0+(1+h)s_1=0. Thus s_(1−h)=0. Conversely every allowed choice of s_h is realized by the empty assignment or a single matching-offset member; an empty class must always have parity zero. This proves sufficiency even when external guards or labels see both class parities separately. An arbitrary function of those parities can be retained. It does not preserve extra observations distinguishing members within a class.

## Exact table proofs for dense b-bit labels

There is a second height-independent degree bound if every quotient has at most k children. For the ordinary label vector L_B in F₂^b, write I(h,z,a;B) for the product of the b+2 affine truth indicators of H_B=h, Y_B=z and L_B=a. For every infeasible table state derive I(h,z,a;B)=0 bottom-up. Use the following basic fact: a multilinear-reduced zero Boolean polynomial of formal degree d is derivable at degree at most d from the Boolean axioms. Reduce monomials one repeated factor at a time. Thus equalities between indicator products that agree pointwise can be used at their formal degrees, without charging the number of variables in their linear factors.

At a leaf, partition the parent indicator into its intersections with x_v=0 and x_v=1. An inconsistent cell is identically zero, and a consistent but illegal cell is its product with the leaf's violated guard polynomial (equal to one on this cell). This costs at most b+5 degrees. A leaf state is tested against the given offset and label.

At an internal node B, partition a forbidden state indicator P by the k child parities and their k label vectors, with literal indicators of linear forms in original variables. A resulting cell W has degree at most D=b+2+k(b+1). If W is identically zero it follows from Boolean axioms. Otherwise the child exterior fields are fixed because H_B and all child parities are fixed. At least one child state is infeasible, since any collection of attainable child states glues to attain the stated parent state. Its indicator F (degree b+2) has already been derived equal to zero. The product WF is derivable at degree at most D+b+2, and pointwise equals W: on a nonzero W all child field, parity and label values agree. Replace it by W using the Boolean axioms. Sum over the partition, whose cells add to P, obtaining the standalone parent row. Evaluating H_B=0 at the root and summing both possible Y_B values gives the indicator of an impossible target label. The original marker equations imply this target indicator equals one (multiply the equations or use a telescoping product), finishing the refutation. A valid direct bound is max(b+5, k(b+1)+2b+4), independent of tree height. This is a degree assertion; expanding every indicator cell can be expensive.

Only the table argument uses bounded label count and arity. The sharper all-marked quotient-proof bound above does not need an arity bound when local PC degrees are supplied.
