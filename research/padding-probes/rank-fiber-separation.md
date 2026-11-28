# One cofactor pivot versus m simultaneous pivots

For m≥1 take a public bit q and m disjoint groups. Each group has x,y,z and the three negative binary pairs enforcing at most one. Include C=(x∨y∨z). On the binary background B its GF(2) failure is f=1+x+y+z. Write g₁=x, g₂=y, g₃=1+z.

For every group, h∈{0,1} and j∈{1,2,3}, introduce a fresh pair s,s′. Put s=s′ and (q=h)⇒(s=0) in B using binary clauses. Add the strict clause (Lⱼ∨s∨s′), where (L₁,L₂,L₃)=(¬x,¬y,z). Its failure on B is gⱼ(1+s); it has the unconditional binary replacement (Lⱼ∨s).

On q=h the three matching-mode s bits vanish. Their three row failures sum to f in each group. Thus {q} gives a fiber-specific certificate. The source has a model with z=1, x=y=0 in all groups and every private bit zero.

For the simultaneous lower bound, consider any global linear identity among the target and auxiliary failures. Vary one s together with its twin, with q unequal to its mode and local x,y,z chosen to make gⱼ=1. Both assignments satisfy B; only that auxiliary failure changes. Every auxiliary coefficient must vanish. Changing one group from (0,0,0) to (1,0,0) then isolates its target coefficient. All failure rows are globally independent. Independence is tested on B models, which can violate the source.

The three local one-hot assignments extend to B with all private bits zero and either q. Pinning any coordinate outside {x,y,z} to a suitable bit preserves all three extensions: use zero for a private bit or a coordinate in another group. Their majority satisfies B and the pin but violates C. Thus that coordinate cannot resolve C individually. Each of x,y,z does resolve C by direct substitution. A simultaneous certificate must select at least one such coordinate per group; m suffice. With zero pivots the fiber rule checks the same global span, so its optimum is exactly one.

The two optima are 1 and m with unconditionally binary-equivalent rows included. This concerns certificate size. The frozen solver implements the simultaneous rule. Other algorithms may use the semantics of the retained clauses.
