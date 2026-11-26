# Negative trace widths on the full theta

For a gate g take the inclusion-minimal independent masks accepted by g among masks with ≤2 points and ≤2 lines. Let T_g be this finite antichain on the original bilateral circuit. On a given full dominating theta, g is warm (noncold) exactly when its survivor set contains at least one member of T_g. Positive flags and masks beyond the stipulated tests play no role. A hitting set for T_g is a negative-specific zero certificate, possibly far smaller than any ordinary zero certificate. Full-theta-physical-credit.md applies with these negative-specific widths, because missing the entire hitting set excludes every possible accepted residual negative.

Uniform nonincident poles x,Y keep each raw with probability (q+2)/N. Two distinct same-shore raws both survive with probability (1+2/q)/N: either Y is the joining line or one point is x and the other lies on Y. For an independent cross pair p,l, its compatible pole choices are x=p,Y=l or a line Y through p and a point x on l off Y. There are 1+q(q+1)=N choices among Nq², hence probability 1/q². The former pair probability is larger for q≥2. By a union bound, if s_g is the number of singleton minimal masks and m_g the number of other distinct minimal masks, then
  Pr[g warm] ≤ min(1, s_g(q+2)/N + m_g(q+2)/(qN)).
One may choose one contained pair per nonsingleton test and union over distinct chosen pairs; this strengthens the count when tests reuse pairs. The same-DAG physical fanout bound therefore requires
  sum_g w_g Pr[g warm] ≥ H−3−(q+2)E/N.
A large fraction of physical sharing must be warm if H is high. This is a quantitative obligation, not a proof that gates with many compatible tests require disjoint producer resources.
