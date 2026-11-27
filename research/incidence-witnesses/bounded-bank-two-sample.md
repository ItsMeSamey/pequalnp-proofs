# Linear-in-q antichain coverage for bounded-width query banks

At k shared incomparable gates in a scalar minimum circuit, let each gate have a query bank B_i of size at most w. On any promised negative, a gate's activation requires that at least one member of its bank be queried. Suppose all actually lost flags except at most r miss at most h of these gates, where the loss is measured on the common cut pinning their outgoing uses to zero.

Let b=h+1. Suppose t is a positive integer, bt≤k−r, 2t≤k, 0<γ<1, γt≥8, and

2 b H(2wt,q) 2^(−γt/2)<1, where H(n,q)=sum_{i=0}^{min(n,q)} binom(n,i).

Then a set of at most q query labels hits strictly more than (1−γ)k banks. This is a conclusion about necessary banks; it does not ensure that one negative activates that many gates.

Assume instead that every Y of size ≤q misses at least γk banks. For a random uniform t-subset S of the sites call it bad if some such Y hits all banks at S. Given bad S, fix any witnessing Y and draw another t sites T from the remainder. Its number of missed banks has hypergeometric mean μ≥γt and variance at most μ. Chebyshev gives probability at least one half of missing ≥γt/2 (the deterministic case is immediate). Thus Pr(S bad) is at most twice the probability of some Y missing no site of S and ≥γt/2 sites of T. Condition on the uniform combined 2t-set, then split uniformly. The restrictions of all Y to its banks induce at most H(2wt,q) patterns since there are at most 2wt raw labels available there. For any fixed pattern missing d≥γt/2 of the combined sites, the chance that all d land on T is ≤2^(−d) by sampling without replacement. This proves the displayed probability bound without a global union bound over all labels.

Partition a uniform permutation into b disjoint t-blocks followed by unused sites. The previous bound and a union bound give a permutation with no bad block. Every block conjunction rejects every negative by its missing bank, while each nonexceptional lost flag activates one whole block. Use the one-cut repair of sparse-antichain-outliers.md: keep only bt sites, append the block DNF and stars for ≤r exceptions. Since bt≤k−r this saves at least one physical gate, contradicting minimality.

**Explicit instance.** If q>100, w≤2, k≥96q, h=1 and r≤k/4, take b=2, t=36q, γ=1/2. Then bt≤k−r and 2t≤k. H(144q,q)≤(144e)^q<400^q by the usual binomial-sum bound; for completeness use (1+q/(144q))^(144q)≥(1/144)^q H(144q,q) and (1+1/144)^144≤e. Thus 4 H(144q,q) 2^(−9q)<1. Some ≤q query labels hit more than half of all k banks, even with arbitrary overlaps.
