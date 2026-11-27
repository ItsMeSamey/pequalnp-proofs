# A smaller common extractor and order 410

Work in the finite-recensus-409.md framework; this note does not change its frozen checker. In the common extractor for one query shore D, mark every signal that is identically zero with those query inputs off on all allowed opposite payloads of size ≤r. Every query raw is marked and no payload raw is marked. An OR is marked exactly when both parents are. An AND with a marked parent is marked; possibly an AND with neither parent marked is marked as well because its parents have different witnesses.

Fold all marked gates and every gate with a marked operand, simplifying the latter on this restricted payload domain. Write R₀ for the number folded, U_D for the fanout sum of query raws, and f for ordinary outgoing occurrences, setting f=0 at the output. If z_g indicates a marked gate and C₁ counts the ANDs with exactly one marked operand, the literal zero-flow identity now reads
```
R₀=U_D+Σ(f_g−1)z_g+C₁+2C₀,
```
where C₀ counts marked ANDs with no marked operands. Indeed Σ of marked operand counts equals U_D+Σ f_g z_g, and a marked zero-operand AND contributes +2 compared with its local baseline of 0−1. Thus R₀≥U_D−1+C₁.

Every tracked AND in the common suffix-product extractor has a marked path predecessor and its other operand accepts a neighbor singleton with zero queries: the flag of its owner's unique path toggles that AND, whereas the sibling is independent of the owner and must be one. Hence at most C₁ ANDs are needed to recover all suffix products. The resulting size is at most s−U_D+1. Distinct reciprocal-free cold owners each consume r physical gates in this very extractor. Summing the two separate shore counts therefore costs at most floor[(2s−U_all+2)/r]≤floor[(2s−2n+S+2)/r]. Use the coarse S₀+2z−m for S in this expression, avoiding circular dependence.

Use the tighter source-group J bound in weighted-envelope-ceiling.md for 3≤t≤8. The scalar finite inequality is
```
(6t−3)(n−p) > [6t−3+(t+1)(γ+(8−t)/(t−1))]u+(t+1)(18G+24p−12B)
```
with γ=(t+4)/(t−2). Increasing B is adverse both when the independent u cap binds and when u=S−B binds: on the latter branch its coefficient is (t+1)[12−γ−(8−t)/(t−1)]>0 for all 3≤t≤8.

At each reset at surplus z' hoist all sole ORs of degree above 2r+2+floor((k−z')/block)+1. The successive preserved allowances suffice because reset expenditures are separated by at least block. At a counting stage z the most recent reset satisfies z−z'<block, so skipped surviving sites have degree ≤2r+4+floor((k−z)/block), and the original full cutoff is a second upper bound. The initial state has no sole ORs. All other estimates and box directions are as in the order-409 manuscript.

Using r=55 and block=768, check-finite-recensus-410.py reaches order 410 with maximum adaptive batch cap 6 and total cap sum 98064. This is an implication for plane parameters; the Bruck–Ryser necessary condition excludes an actual plane of order 410 only if 410 fails to be a sum of two squares, which it does not (410=19²+7²). No construction of such a plane is used.
