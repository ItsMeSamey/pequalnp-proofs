# Pinning gates with near-linear false-pair matchings

Fix N=q²+q+1, q≥4, and m disjoint nonincident singleton pairs accepted by one physical monotone gate. For a uniform q-set of lines with its maximal independent payload, integer L≥1 and µ=mq/N, the probability the gate is zero is at most

    (N+1)(exp(−µ/128) + exp(−µ/(256(L+1))) + N(2e/L)^L).

First choose lines independently with probability p=q/N. Each matched owner line y has a distinct matched off-line point p_y. Let U be the number of selected owners, V the number of selected owners whose points lie on selected lines. E U=µ and E V=(1−(1−p)^(q+1))µ≤3µ/4, since p≤1/(q+1) and (1−1/(q+1))^(q+1)≥1/4. If U>V the gate accepts.

Let W count the maximum number of selected owners assignable to selected covering lines, with capacity L per covering line. Always W≤V. If every line has at most L selected matched predecessors, W=V. Predecessor counts are dominated by Binomial(q+1,p) because the matched points are distinct. Probability of overload is at most N(2e/L)^L by the union bound on predecessor subsets.

Forcing coordinate i absent reduces W by d_i≥0. Fix one optimal assignment on this sample. Removal of i can destroy only edges incident to i. Thus each d_i≤L+1 and Σd_i≤2W. By entropy tensorization for independent coordinates, for λ>0,

    Ent(exp(λW)) ≤ E[exp(λW) Σ(exp(−λd_i)+λd_i−1)]
                  ≤ λ²(L+1) E[W exp(λW)].

For the first inequality bound conditional entropy in each coordinate by E_i[X(log X−log a)−X+a] using a=exp(λ(W−d_i)), independent of that coordinate. The second uses exp(−t)+t−1≤t²/2 and Σd_i²≤2(L+1)W. For ψ=log E exp(λW) this gives (ψ/λ)'≤(L+1)ψ'. Integrate from zero, where ψ/λ tends to E W, giving ψ≤λ E W/(1−(L+1)λ) for 0<λ<1/(L+1). Take λ=1/(16(L+1)). Then ψ≤(4/5)λµ, so Pr[W≥7µ/8]≤exp(−3µ/(640(L+1)))≤exp(−µ/(256(L+1))). The binomial Chernoff bound gives Pr[U≤7µ/8]≤exp(−µ/128). Union with overload gives the independent-sample failure estimate. The selected size has q as a binomial mode, so conditioning on exactly q lines costs at most N+1.

For each desired power A take L=ceil(C_A log q/log log q) with C_A large enough. If m/(q(log q)²/log log q) tends to infinity, the failure probability is below q^(−A) for all sufficiently large orders. The proof parameter L does not change the failure event. In polynomial-size DAGs, all gates passing one common matching threshold may be pinned to one simultaneously, preserving all flags and every independent negative of any fixed rectangular size, by the extension argument of simultaneous-dense-pair-pinning.md. Removed gates are counted once each. This is a false-pair matching condition, not a condition on true flags.
