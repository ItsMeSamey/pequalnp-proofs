# A call bound for monotone, shore-separated exact-slice reductions

Let D be any monotone Boolean oracle on point and line masks of a plane of order q≥2 that agrees with incidence on all inputs with exactly q selected query lines. A reduction forms the OR of branches
     
    a(P) AND b(Y) AND D(Ψ(P),Φ(Y)).

Both Boolean guards and the coordinatewise mask maps are monotone; each depends only on its indicated shore. Different branches may choose different maps and guards, fixed independently of D. Suppose the reduction must compute incidence for all point payloads and |Y|≤q for every admissible oracle. Then it requires at least ⌈N/3⌉ oracle branches, N=q²+q+1. The bound concerns oracle occurrences even if the preprocessors share arbitrary physical logic.

Use D₋=incidence AND [query weight ≥q] and D₊=incidence OR [query weight >q]. Fix one branch, and let A be the set of raw points p such that a({p})=1. Call a raw line l relevant when b({l})=1 and its codeword Φ({l}) has size at least q. Every branch flag under D₋ must belong to A times the relevant lines. If |A|≤1 there are at most q+1 such flags.

Any relevant line of codeword size >q is incident with every p∈A: otherwise D₊ would accept a target-negative singleton pair. Partition the remaining relevant lines by equality of their size-q codewords. For one class C with codeword Z, let A_Z consist of the p∈A for which Ψ({p}) meets a line in Z. The branch flag relation in this class is exactly A_Z×C. D₊ prevents any nonincidence in that rectangle; codegree one thus bounds it by q+1 flags. This remains true for completely arbitrary point-mask transformations within the stated shore restriction.

For any p∈A, all its nonincident relevant lines must lie in at most one exact-q class. Indeed, if l and j miss p and have different size-q codes, the monotone mask Φ({l,j}) contains both codes, of union size >q. The query guard is also true by monotonicity. Thus D₊ accepts an independent two-line target input, a contradiction.

Choose two distinct points p,p′∈A. Remove the at most two classes containing the respective nonincident relevant lines. Every remaining relevant line passes through both p and p′; by unique joining there is at most one such raw line, contributing at most q+1 genuine flags. The two removed classes contribute at most 2(q+1) flags. Thus a branch covers at most 3(q+1) flags under D₋. The OR on this oracle must cover all N(q+1), proving the claim.

The sharper ⌈N/2⌉ bound for direct raw restriction with fixed padding uses the extra structure of those maps (fixed-padding-or-black-box-bound.md). Neither argument handles arbitrary mixed point/query preprocessing, non-OR output aggregation, ancillary non-oracle flag detectors, or a reduction tailored to a particular oracle's off-slice behavior.
