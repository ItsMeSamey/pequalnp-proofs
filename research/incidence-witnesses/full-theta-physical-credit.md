# Cold fanout on a dominating theta

On the original live, sole-AND-normalized bilateral DAG choose a nonincident point x and line Y, and retain x, Y and all their neighbors. Set the complementary raw set D to zero. The induced graph is theta with q+1 arms and n=2(q+2) raw vertices. The original circuit on it must have size at least 4(q+1)=2n−4 even on its two-by-two independent negative masks and positive flags (theta-residual.md). Every deleted point has a retained neighbor, its join to x. Every deleted line meets Y in a retained point. This uses the complete arms, not a truncated pencil.

Use blocker-basket.md's cold normalization with this common residual family and C the gates rejecting each of its negative masks. It saves at least U_D+F_C+c_1 slots, with every deleted sole raw's private AND contributing to c_1 since its sibling accepts a retained neighbor singleton. Hence U_D+c_1≥2|D|+E_D without any pin deficit. For δ=s−(4N−4), each individual restriction satisfies δ≥F_C+E_D.

Uniform nonincident poles retain each coordinate with probability (q+2)/N. For q=401 choose, for each internal nonoutput gate, a set of z_g inputs whose simultaneous zero forces this gate to zero. It is cold with probability at least (1−403 z_g/N)_+. With w_g=f_g−1, E total raw excess beyond two and H the sole-read count, linearity and F=sum w=δ−3+H−E yield respectively

    N δ ≥ (N−403)E + sum_g w_g max(0,N−403 z_g),
    sum_g w_g min(N,403 z_g) ≥ N(H−3)−403E.

Each selected pattern is a single physical experiment. No gate-count aggregation assumes disjoint supports or independent coordinate survival. Geometry, compensation, and the inequality independently verified by /root/incidence/audit. Arbitrary dense semantically middle gates remain an open case.
