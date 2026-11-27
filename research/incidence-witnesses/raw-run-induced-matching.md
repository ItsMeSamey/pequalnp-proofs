# Induced matchings at ends of first homogeneous runs

Consider any live binary monotone AND/OR DAG computing projective-plane incidence on arbitrary point payloads and at most q lines (N=q²+q+1). For each gate type b mark as endpoints all b gates with an outgoing occurrence to the other type, and the output if it has type b. Make the bipartite relation from point raws to these endpoints: p reaches e by a path using only b gates after the raw. Count individual physical endpoints even with arbitrary sharing. Let d_O,d_A be the maximum induced matching sizes of the OR and AND relations, respectively. They are not ordinary matching sizes. Along every raw-to-output path the end of its first homogeneous run is a marked endpoint.

Choose a uniformly random distinguished point p, and t other uniformly random points H, with 0≤t≤N−2. Set these H points high and all points outside H and p low, leaving p free. If some line l through p misses H, set l on and all other queries off. With p off the resulting test is independent; with p on it contains a flag. A change at the output therefore follows a directed path of changed signals from p, by tracing changed inputs backwards from the output. Its first-run endpoint changes. If this run is OR, no point in H can have a pure OR path to the endpoint, since such a path would already force it on. If it is AND, none of the low points can have a pure AND path to it, since such a path forces it off. The argument counts possible propagating paths, without assuming each marked endpoint is sensitizable.

For the OR alternative condition on T=H union {p}. Each successful candidate p in T has an endpoint whose neighborhood intersects T in exactly {p}. Selecting one such endpoint per candidate is an induced matching: endpoints are distinct and all cross incidences are absent. Given T, p is uniform, hence this alternative has probability at most d_O/(t+1). For the AND alternative condition on H. The complement consists of the low points and the uniformly chosen p, so the same reasoning bounds its probability by d_A/(N−t). These arguments apply with t up to N−2 even though only one point per experiment is left free.

Given p, its q+1 lines partition the N−1 other points into q+1 bins of q points each. A bin empty of H gives the required surviving line. Write
    μ=(q+1) binom(N−1−q,t)/binom(N−1,t).
Emptiness of two bins is negatively correlated: conditional on missing the first, the sample is uniform on a smaller population with the same q forbidden points in the second. Thus the count X of empty bins satisfies Var(X)≤μ. For μ>0 Cauchy gives Pr[X>0]≥μ/(1+μ). Also X>0 deterministically when t≤q. We obtain
    d_O/(t+1)+d_A/(N−t) ≥ Pr[X>0] ≥ μ/(1+μ).
Taking t=floor(q(log q−log log q)), natural logarithms, gives μ=(1+o(1))log q: the log miss probability is −tq/(N−1)+O(log²(q)/q). Consequently
    d_O/(q log q)+d_A/N ≥ 1−o(1).
This final formulation uses boundedness when passing to the slightly different denominators: if either normalized summand is ≥1 the stated bound already holds; otherwise the denominator changes cost o(1). No automorphism or subfield assumptions are used. In fact the proof on the point shore needs correctness only on arbitrary point payloads and a single query line.

On the line-raw shore the same argument with t=q−1 selected high lines respects the q-line cap after the distinguished query toggles. Each free line retains a point outside the ≤q−1 other lines, and so
    d_O(line)/q + d_A(line)/(N−q+1) ≥ 1.
These structural bounds concern reachability in original physical homogeneous runs. They do not alone assert a superlinear gate count.
