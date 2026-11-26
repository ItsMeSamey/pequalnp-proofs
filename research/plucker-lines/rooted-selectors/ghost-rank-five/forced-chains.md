# Two chains of forced columns on a rooted circuit

Let every true anchored pair have the same total weight and suppose both dual marginals d(q)=b occur. Fix any original circuit C through t in a model of marginal b. Its span avoids s. If q were outside span(C,s), varying the dual at fixed C would change the total, so there is a unique subset A⊆C omitting t with

    q = b s + Σ_{e∈A} v_e.

Here and below s in a vector equation denotes the column v_s. Uniqueness uses that C minus t is a basis of span C. Every functional killing C and taking value one on s therefore has marginal b.

Call an ordinary column z forced in this marginal if d(z)=1 in every true model of marginal b. In particular this holds for every anchored dual at C. Hence z=s+Σ_{B_z}v_e for a unique B_z⊆C omitting t. A forced column is outside C. Define h_z=ℓ_z+ℓ(B_z). **For fixed h the subsets B_z of the forced columns form a chain under inclusion.** Thus no three forced columns have pairwise incomparable representing subsets on the same true rooted circuit. For fixed zero-labeled contraction columns the color h_z is the value at z+s of the common linear interpolant of ℓ on C minus t.

Indeed, take two incomparable B_z,B_w. Put R=B_z△B_w and form the original rooted cycle

    X = (C minus R) ∪ {z,w}.

It contains t, and its sum is zero because v_z+v_w is the sum over R. Pick e∈B_z minus B_w and f∈B_w minus B_z. On span C set a functional to one at exactly e,f among C, which is consistent with the unique relation on C. Set its value on s to one and extend to the ambient space. It takes zero on z,w and all of X. Its q-value differs from b by [e∈A]+[f∈A], while the primal weight difference is h_z+h_w. If e,f belong to the same A-part, the new model stays in marginal b and clears both forced columns, a contradiction. They therefore belong to opposite parts, and stationarity forces h_z+h_w=1. This proves the chain claim. It also shows directly that the B_z are nested separately on each of A and C minus A, even without consulting the weights.

This argument provides an explicit bypass: any opposing pair e,f of the same A-part clears z and w while retaining the original marginal. For opposing e,f in different A-parts the new total weight changes exactly when h_z=h_w. These conclusions only need z,w outside C,s with the indicated vector representations; the construction itself does not require forcedness.

For a first-rank counterexample to the quotient-switch conjecture, every named ordinary contraction element is forced in at least one marginal. Otherwise contract an element killed by some model of each marginal, preserving both marginals, stationarity, and the positive switch in smaller rank. Choose any assignment of each contraction element to a marginal in which it is forced. In a stationary example each assigned family must pass the two-chain test on every rooted circuit in that marginal. This condition is necessary, and no assertion of sufficiency is made.
