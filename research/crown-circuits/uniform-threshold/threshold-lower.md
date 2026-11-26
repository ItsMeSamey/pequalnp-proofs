# A proposed uniform gate lower bound for threshold two

Let C(n) be the minimum number of binary AND and OR gates with unrestricted fanout that compute threshold two on n ordinary Boolean inputs. The proposed inequality, for every n≥2, is

    C(n) ≥ 2n + (4/3)√(n+3) − 6.

This research proof uses the classical OR-only cost lower bound 2k−4 for threshold two on k≥2 inputs. Its square-root coefficient is being independently audited.

## Reducing to two OR readers at each raw

Take a globally minimum circuit. Remove dead gates, constants, repeated operands, and unary identities. A gate equal to an earlier wire could be bypassed. We may take a representative with no OR that combines a singleton-clean signal (false on every singleton) and a singleton-hot signal. Bypass each such OR to its hot input and adjoin its clean input to the output as a disjunct. This uses at most one new OR per bypassed OR. On a singleton, the modified wires have the old values. On any positive assignment where the bypassed network would reject, take the first wire whose value changed: it must be a bypassed OR, and its previously unchanged clean input is true. The added disjunction accepts. The empty assignment is preserved. Consequently the resulting circuit is still globally minimum. Unused wires or duplicates would contradict minimum size.

For n≥3, a raw variable with at least three readers saves at least three gates when set false. If a raw x has two readers and one is an AND g=x∧P, that AND vanishes together with its other raw reader and a consumer of g. The consumer cannot be the other reader of x, because any gate joining x with g≤x is redundant. Nor can g be the output, because after x is set false the threshold is still nonzero.

If x has only one reader x∨P, then P is independent of x and must reject each other singleton y: otherwise y and x+y would give identical output. It rejects singleton x too, so this is a prohibited mixed OR. If the sole reader is x∧P, then P must accept every other singleton from the same comparison y against x+y. Thus P is the disjunction of all other variables. Its root is a gate since n≥3. On x=false, remove x∧P and a distinct downstream consumer; also eliminate the distinct root computing P. Every residual AND taking P simply copies its other operand, every residual OR taking P computes P, and these substitutions propagate. The residual output is threshold two, distinct from P, so P can be removed. Every raw is essential for threshold two with n≥2. Hence for n≥3 either C(n)≥C(n−1)+3, or a minimum representative has exactly two readers per raw, both OR gates.

## Formal graph for a regular representative

Write C(n)=2n+s and a for its AND count. Flatten the private OR trees ending at each shared OR, each single-use OR feeding an AND, or the output. Every group has k raw slots and t nonraw slots and costs k+t−1 ORs. Its nonraw slots come from other groups or ANDs. A repeated raw within a group is redundant by idempotence. Two raws cannot occupy the same pair of groups: on the singleton of either, both groups already fire, and adding the other cannot affect the output. Thus each raw is a distinct edge of a simple graph G, including precisely those groups with positive raw count as vertices. Write v,c,Δ for the number of vertices, connected components and maximum degree. Every component has at least two vertices.

Replace each nonempty batch of raw slots by a fresh formal input pin for its group. A pure group becomes a wire and a mixed group with a raw batch now costs t ORs instead of k+t−1. A group with no raw batch is retained. The total number of ORs drops by exactly Σ_nonempty(k−1)=2n−v. The resulting formal circuit therefore has s−a+v ORs and still gives threshold two on the selected edges when its formal pins are set to their incident-edge indicators.

Each unshared group root other than the output feeds an AND operand, so the number of unshared roots is at most 2a+1. There are at most s+1 shared internal gates: of 2(2n+s) operand occurrences, 2n come from raw inputs and 2n+s−1 are the mandatory first uses of nonoutput gates. The rest total s+1. Hence

    v ≤ 2a+s+2 ≤ 3s+10,

because the physical OR bound 2n−4 implies a≤s+4. In particular s≥−4.

## Star and component counting

For k=Δ≥2 pick a vertex U of degree k. In its component root a spanning tree at U containing all k incident edges. Peel vertices farthest first except U and its neighbors. For any peeled V two steps toward the root give V−W−Z. The singleton WZ and the pair WZ,WV set the same formal pins apart from V and have opposite outputs. All pins removed earlier are false in those tests. Therefore V is essential. Setting this pin false saves an OR: along a live occurrence-to-output path its first OR is bypassable by propagation through the preceding ANDs; an AND-only path would force output zero, contrary to the retained nonzero star specialization.

In each other component leave an anchor edge. Peel the other vertices toward it by the same two-edge witness. When only the two endpoints remain, compare a singleton in U's star to its union with that anchor edge. Only the two endpoints change and the outputs differ. At least one endpoint is essential (possibly with the other endpoint set true). Set that endpoint false first, saving an OR, then set the other false for free. These steps save at least one OR per remote vertex except one in each component. Each restriction is applied to the already simplified circuit and uses still-available witnesses, so no saving is charged twice.

In total at least v−c−k ORs are saved. Finally set U=true, keep its k neighbors as independent raw star variables and all other pins false. Every nonempty star input has the same pin values as the physical edge selection. The empty input rejects by monotonicity and singleton rejection. Therefore the star computes threshold two and needs at least 2k−4 ORs. The accounting yields

    Δ ≤ s−a+4+c.

This also holds for Δ=1 since s−a+4≥0 and c≥1.

For a component with j≥2 vertices its edge count is at most 1+(j−2)(Δ+2)/2. For 2≤j≤Δ+1 this is the chord above j(j−1)/2. For j≥Δ+1 it dominates jΔ/2. Sum over components:

    2n ≤ 2c + (v−2c)(Δ+2)
       ≤ 2c + (s+2d+2)(s−d+6),      d=a−c.

Both factors are nonnegative. Their weighted sum, first plus twice the second, is 3s+14, so the product is at most (3s+14)²/8. Since 2c≤v≤3s+10,

    16n ≤ (3s+14)² + 8(3s+10) = 9(s+6)²−48.

This proves the desired regular-case lower bound. For n=2, C(2)=1 suffices. If the deletion alternative holds, induction suffices because (4/3)(√(n+3)−√(n+2))≤1 for n≥3.

## Literature comparison

Sergeev established the asymptotic order 2n+Θ(√n). The SAT 2026 paper quotes a general lower bound 2n+√((2n−4)/3)−19/6 and proves an upper bound 2n+√(2n)+O(n^(1/3)). Consequently a universal matching lower bound with the balanced grid's second-order coefficient 2 is false. The proposed coefficient 4/3 would narrow the gap to the upper coefficient √2. This comparison does not establish priority.

[Sergeev, On the complexity of monotone circuits for threshold symmetric Boolean functions](https://doi.org/10.4213/dm1547). [SAT 2026, section 3.4 and Theorem 9](https://drops.dagstuhl.de/storage/00lipics/lipics-vol377-sat2026/html/LIPIcs.SAT.2026.23/LIPIcs.SAT.2026.23.html).
