# Arbitrary occupancy partitions

Suppose points and lines each have a supplied partition into buckets of size at least q. The two partitions need not be geometric and need not be related. Suppose all shared internal gates of a sparse-correct circuit depend only on the occupancy bits of these two partitions. For any fixed 0<alpha<1, the circuit size is at least

    [(1−alpha)(exp(−alpha)−exp(−2alpha))²−o(1)] Nq.

At alpha=0.4 the coefficient exceeds 0.029, so this proves the requested bound for all sufficiently large orders under this sharing hypothesis.

Take k=floor(alpha q) uniform distinct lines as padding T0; let U be the points avoiding T0. Take P0 as k uniform distinct points of U. This is possible for all large q because |U|≥N−k(q+1). Retain a free point/line only if its own bucket is already hit by the pad of the same polarity, it is not a pad and it avoids the opposite pad. All occupancy bits are constant after this restriction. As a test graph start with the original incidence graph with k perfect matchings removed, then keep only free vertices. Every proper-neighborhood test uses at most q−k additional lines, so is legal on top of the pads. Its two free parts have no incidence even in the original graph. As before the surviving number of edges lower-bounds the restricted formula leaf count.

Set eps=q^(−1/4) and m=floor((1−eps)q). Except for O(N/eps) flags (p,l), the bucket of p has at least m points outside l and the bucket of l has at least m lines not through p. Indeed for a fixed point with bucket size b≥q, a failing l must contain at least b−m other bucket points, while the numbers on its q+1 incident lines sum to b−1. Thus there are at most (b−1)/(b−m)≤1/eps such lines. The line-side claim is dual. For each good flag choose sets A,B of exactly m such points and lines. The first pad avoids the star of p and hits B with probability at least exp(−alpha)−exp(−2alpha)−o(1), by the difference between the two hypergeometric avoidance probabilities for disjoint sets of sizes q+1 and m. The error is uniform. For sizes j=(c+o(1))q this follows from the product over i=0,...,k−1 of (1−j/(N−i)), whose logarithm is −alpha c+o(1).

For any point set D let X_D=|D intersect U| and f=Pr(p in U)=exp(−alpha)+o(1). Distinct point-survival indicators are negatively correlated: their joint survival probability uses the union of two stars of size 2(q+1)−1. Factor by factor it is at most the product of individual survival probabilities, since (N−2C+1−i)(N−i)≤(N−C−i)^2 for C=q+1, as N−i≤C². Thus Var X_D≤|D|. Chebyshev shows that with probability 1−o(1), simultaneously |U|/N=f+o(1), |U intersect l|/q=f+o(1), and |U intersect A|/q=f+o(1). This statement is uniform over flags and chosen A. Intersecting it with the first-pad success condition loses only o(1) probability.

Condition on this event and expose P0. The subsets U intersect l and U intersect A are disjoint. By the same hypergeometric difference, P0 avoids l and hits A with probability at least exp(−alpha)−exp(−2alpha)−o(1): although the population shrank by a factor f, both relevant set sizes shrank by the same factor. The two padding successes ensure the flag survives, including absence of either endpoint among the pads. Starting with N(q+1−k) flags after matching trimming and removing only o(Nq) bad flags gives the stated expectation. A restriction attaining at least its expectation exists.

## Uniform verification starting at order 401

For q≥401 take k=floor(3q/8) and m=q−ceil(q/13). Use the previous construction and choose exactly m eligible members in each of the two pertinent buckets for each good flag. The perfect-matching trim and at most 26N bad flags leave more than 0.56Nq flags, since (q−1)/(q−m)≤13. We have 0.372q≤k≤0.375q, m≥0.92q, C=q+1≤1.003q and N≤1.003q².

The common point survival probability f obeys 0.685<f<0.691. Indeed exp(−kC/(N−k−C))≤f≤exp(−kC/N), using −x/(1−x)≤log(1−x)≤−x; N−k−C=q²−k gives the claimed bounds. Given that star(p) is missed, the conditional chance of hitting the m-line subset outside that star is at least 1−exp(−km/N). Thus the first-pad success probability is greater than 0.197.

For the concentration step require |X_all−fN|≤0.025N, X_l≤fC+0.2q, and X_A≥fm−0.15q. Since each variance is at most one quarter of its set size, Chebyshev and a union bound bound the failure probability by
    400/N+6.27/q+11.12/q < 0.046.
Therefore at least 0.151 probability remains jointly with the first successful padding. Now 0.660N≤|U|≤0.716N, X_l<0.894q, and X_A>0.480q. The k random points from U avoid l with probability at least
    exp(−k X_l/(|U|−k−X_l)) > exp(−0.511) > 0.599.
Given avoidance, the chance of hitting A is at least
    1−exp(−k X_A/|U|) > 1−exp(−0.248) > 0.219.
This last conditioning can only shrink the eligible population while preserving A. Hence each good flag survives with probability greater than 0.151 times 0.131. We obtain s+1>0.56·0.151·0.131Nq>0.011Nq, enough for 100s≥Nq throughout q≥401.
