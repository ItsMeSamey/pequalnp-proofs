# Counting differentiating arms in singleton-flag protocol fragments

Use the gate-local KW routes and physical fragments of physical-fragment-rank-transport.md. For a shared gate b other than the output, each outgoing physical operand occurrence a belongs to that gate alone. Let A_a be the native flags e for which some proper-neighborhood column sends the protocol through that occurrence. Let m(v,b) count the raw v occurrences in the fragment rooted at b. For the root r let U_r be its number of raw pins.

Then N(q+2) ≤ U_r + Σ_b Σ_{a out of b} Σ_{(p,l)∈A_a} [m(p,b)+m(l,b)].

Indeed, on each star(v) square, the arrival indicator at b is the sum of its disjoint incoming protocol receipts through the outgoing circuit pins a. Each receipt matrix has rank at most its number of supported rows, at most |A_a ∩ star(v)|. Within a fragment, following the unique physical path to a raw occurrence applies row and column restrictions to the arrival matrix. Root arrival has rank one. Apply these facts to the fragment ledger and interchange the finite sums. This charges each outgoing occurrence in one fragment term with its stated weight.

If each nonroot m(v,b)≤d and |A_a|≤t then N(q+2)≤(4dt+1)s+1, using at most 2s outgoing operand occurrences and U_r≤s+1 in a trimmed physical binary DAG. Thus dt≤24 suffices for 100s≥Nq. More generally, choose one high-rank pin at each of a set H of distinct sites. If the chosen restricted arrival ranks are r_v>1, their fragments are nonroot and Σ_H r_v≤2Σ_a |A_a|, or with coefficient one if H lies on one shore. Each responsible pin is counted once per eligible endpoint of an active flag, independent of its number of witnessing columns.

Separately for any fixed tie rule and 0≤R<q+1, let H be the sites with at least one restricted pin-arrival rank exceeding R. The final return-v matrix on its own star has rank at most q+1 for high sites, and at most R times the number of v pins otherwise. Hence |H|≥[N(q+2)−R(s+1)]/(q+1−R). This uses the rank cap on the final site matrix before summing pin bounds.

The compressed pivot shows why an outgoing arm can have many supported rows despite small direct fanout. The weighted bound assumes no uniform arm cost on arbitrary circuits. A universal incidence lower bound still needs new control of the total physical weights or a different invariant.
