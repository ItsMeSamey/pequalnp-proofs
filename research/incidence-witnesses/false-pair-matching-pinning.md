# Pinning mixed gates with large false-pair matchings

Let N=q²+q+1 and q≥4. For a physical monotone gate g, suppose m pairwise vertex-disjoint nonincident pairs are accepted on singleton masks. For a uniform q-line set S and its maximal independent point payload, any integer L≥1 gives

    η = min(1, N(2e/L)^L),   h = max(0, mq/(4N)−qη),
    Pr[g is zero] ≤ η + exp(−h²/(2q(1+L)²)).

Write p_y for the point matched to y. Let F(S) count the selected matched lines y whose p_y is on no selected line. Each contributes an accepted pair. Given y selected its point remains uncovered with probability at least 1/4 by the product calculation in random-query-supergraph-filter.md. Thus E F ≥mq/(4N).

Call S good if for every line z at most L selected matched lines have their points on z. At most q+1 matched lines are eligible for each z. The chance of hitting at least L is bounded by binom(q+1,L)(q/N)^L ≤ (2e/L)^L, by enumerating L-subsets. The probability of a bad set is at most η. For two good q-sets S,T let k=|S minus T|. At most k counted lines y disappear from S; a retained counted y no longer counted in T has its point on a line of T minus S. At most kL such y exist, by goodness of S. Reversing roles proves |F(S)−F(T)|≤(1+L)k. This does not require a swap path through good sets.

When η<1, extend F to all samples using the infimum of F(T)+(1+L)|S minus T| over good T, then clamp to [0,q]. This extension agrees on good sets, is (1+L)-Lipschitz, and has expectation at least E F−qη. After fixing a prefix of the ordered sample, any two alternative next draws are coupled by transposing their labels in the completions. The resulting sets differ by at most one swap, bounding each conditional-expectation increment by 1+L. Azuma's inequality and the probability of bad samples give the claimed estimate. If η=1 it is immediate.

Set L=ceil(log q). If m/(q^(3/2)(log q)^(3/2)) tends to infinity, the zero probability is smaller than every fixed inverse power of q. In any polynomial-size DAG one can simultaneously replace every gate with such a matching (using one common lower bound m) by one, propagate constants, and save at least one physical gate for every designated gate. The resulting circuit still accepts all flags and rejects every independent negative of any fixed rectangular size (a,b): compare the superpolynomially small probability of any designated failure with the polynomial lower bound for extension of each fixed negative from simultaneous-dense-pair-pinning.md. These are a fixed set of wires chosen using their original profiles.

A full off-incidence matching has only N false pairs, far below a positive fraction of all Nq² nonflags. A matching of true incidence flags does not qualify.
