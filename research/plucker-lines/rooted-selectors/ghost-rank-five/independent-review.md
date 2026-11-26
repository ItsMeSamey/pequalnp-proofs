# Independent review of the rank-six finite test

The rank-six search checks the conditional soundness of a positive projected switch when both genuine dual marginal values occur. It assumes the named chart reduction and the zero-defect endpoint lemma. Its conclusion concerns the survival of a switch in this rank.

## Reconstructing the fiber clauses

Gauge the root label to zero. For d(s)=1 and d(t)=0, put e=d(q). Among ordinary columns annihilated by d, a subset summing to t gives a rooted cycle after adjoining the distinguished occurrence t. Its primal weight is the sum of the selected ordinary labels. Consequently stationarity is exactly the exclusion of (t,1+e) from the span of the available labeled columns (v,w) in V⊕GF(2). There is no requirement that an ordinary occurrence at vector t be excluded: the distinguished occurrence has been removed separately.

A separating functional (f,η) must evaluate to one at (t,1+e) and vanish on every eligible labeled column. If η=0 this says f(t)=1 and f(v)=0; if η=1 it says f(t)=e and f(v)=w. In both cases f and f+d give identical values on all tested vectors and on t. Thus keeping one f per pair is exact. Mandatory incompatible f are discarded. If a surviving certificate selector is set, every incompatible optional typed column is forced absent; the per-d disjunction demands at least one such certificate. The reverse clauses for a selector are unnecessary, as its value is existential.

A marginal is genuine precisely when t is in the span of the selected ordinary d-zero vectors. Every f with f(t)=1 must take one on some such vector. Any f already hitting a mandatory vector needs no clause. For each remaining f the program forces one of its optional hits whenever this d is designated as a marginal witness. A disjunction separately for e=0 and e=1 requires both values. Repeated ordinary copies with identical (v,w) leave both required spans unchanged, including the possibility that their vector equals the distinguished t. Allowing one occurrence of each optional type is therefore exact.

The coordinate chart uses independent s,i,k, two ordinary contraction coordinates and q. The two endpoint lift defects fix the q coefficient of t to one and give equal q coefficients on j and l. The three ordinary contraction masks are arbitrary two-bit vectors. The normalized cases therefore number 4³×2=128 before quotienting by contraction-coordinate permutations. The independent rerun used all 128.

## Reproduction

The unmodified command `python -B finite_types.py 6` returned UNSAT on every chart. The separate proof driver `verify_rank6.py` intercepts the exact original clause lists, emits DIMACS, asks Glucose4 for an UNSAT trace, and verifies each trace with a separate drat-trim executable. It uses standard python-sat and accepts an output directory plus `--drat-trim PATH`. Its manifest fields are chart, CNF clause count, DRAT line count, CNF SHA-256, DRAT SHA-256, and verification status. Each four-digit chart key lists alpha, beta, delta and gamma in that order.

The audited finite_types.py has SHA-256 `13776d521349acc71c271a06a0b6302e92a1fbfcdd98f7a8a21a3fa3ad3734d2`. No discrepancy was found between the chart clauses and their span conditions.

All 128 Glucose4 traces passed drat-trim. The [per-chart manifest](rank6-proof-manifest.txt) records every CNF and proof hash. Chart keys were checked against the full Cartesian product and both hashes were recomputed from the saved files.
