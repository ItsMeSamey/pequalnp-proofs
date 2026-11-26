# Exhaustive fiber classification at fixed rank

A stationary original instance has ℓ(C)+d(q)=b on every anchored model. Add b to the label of the distinguished cycle root t to normalize b=0. For each d with d(s)=1,d(t)=0, write E_d for its zero columns, including t. One of two linear certificates always exists.

* If the cycle fiber is empty, t is outside the span of E_d minus t. There is a functional f taking value one on t and zero on all those other columns.
* If the fiber is nonempty, all its cycles through t have ℓ-weight d(q). These cycles span the entire cycle space on E_d: subtracting any one of them realizes every cycle avoiding t as a difference. Hence ℓ+d(q)[t] is in the row space on E_d. Equivalently f(v_e)=ℓ_e+d(q)[e=t] on all its columns.

Conversely an inactive certificate rules out the fiber, and an active certificate enforces its prescribed weight. Declaring an empty fiber active is harmless. Explicit representations of t by the other d-zero columns for one d at each q-value ensure that both genuine dual marginals actually occur.

Use the ordinary chart basis vectors s,i,k,Z and the freely contracted q as an ambient basis; Z denotes the list of ordinary contraction elements. If both quotient endpoint circuits have lift defect one, write their six named ordinary vectors as

    s, i, k, t=i+k+α+q, j=s+i+β+γq, l=s+k+δ+γq,

where α,β,δ lie in span Z and γ is a bit. Indeed the two endpoint defects agree just when the q-coefficients of j and l agree. If an endpoint has zero defect it already gives true mixed variation by the [virtual contraction lemma](../virtual-contraction.md). Adding a row functional to ℓ leaves every cycle weight unchanged. Gauge ℓ to vanish on s,i,k,Z and then on t using the remaining q coordinate. The positive switch says exactly that the labels of j,l differ in this gauge. Exchange the two peripheral branches to set those labels to zero and one in that order.

The [SAT program](check.py) includes the named chart positions as mandatory occurrences. It also allows an optional ordinary occurrence for each possible typed vector (v,ℓ). Additional occurrences are unnecessary: after removing repeated copies of the same typed vector, stationarity is inherited by restriction, and each of the two actual root representations still exists because identical columns leave the ordinary span unchanged. The distinguished t is represented separately from its optional ordinary copies. Any desired q is a valid dual moment because the mandatory columns span the ambient space. Shannon variables select the optional columns and the two kinds of certificate. Parity equations are encoded using ordinary four-clause XOR gates. Each asserted marginal has its own explicit subset of zero columns summing to t.

In dimension five there is one ordinary contraction coordinate, so there are 16 charts after the gauge normalization. With python-sat installed, `python -B check.py 5` returns UNSAT on every chart. The [ground-set enumeration](ground-enumeration.md) is independent of SAT. The same construction produces a finite exact test at any fixed rank r≥5, with 2·2^(3(r−4)) normalized charts. A run at a larger rank establishes a result only after all its charts have been decided.

## Rank six by explicit separator tables

The [finite-table implementation](finite_types.py) eliminates the XOR gates. For each d, enumerate one representative of each pair f,f+d, since the two agree on every d-zero vector. An inactive certificate forbids precisely those optional columns with f(v)=1 and d(v)=0, and requires f(t)=1. An active certificate requires f(t)=d(q) and forbids each d-zero optional column with f(v) different from its label. Discard certificates inconsistent with mandatory ordinary columns. A disjunction over all surviving certificates expresses stationarity for this d. Separately, whenever d is used to certify a marginal, require at least one present column meeting each otherwise-possible inactive separator; this is exactly the criterion that t lies in the span. Test the two marginals separately as above.

Running `python -B finite_types.py 6` rejected all 128 normalized charts. Thus every positive quotient switch with both true dual marginal values is sound in ambient rank six as well. The optional `--orbits` flag identifies permutations of the ordinary contraction basis: each coordinate of Z has a binary triple of coefficients in α,β,δ, and only the multiset of those triples is needed.

The original XOR-gate implementation separately rejected all 128 rank-six charts. At rank seven the explicit table implementation rejected all 240 permutation orbits, covering 1,024 raw charts. Reproduce the rank-seven result with `python -B finite_types.py 7 --orbits`. Thus an arbitrary-rank common contraction as in the [asymmetric linkage note](asymmetric-linkage.md) suffices whenever it leaves ambient rank at most seven.

The rank-six archive contains independently checked DRAT proofs for every normalized chart. The rank-seven result uses a complete SAT-solver replay over 240 symmetry classes representing 1,024 charts. This release supplies no rank-seven DRAT verification.
