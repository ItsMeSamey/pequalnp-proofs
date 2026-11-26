# A shared vertex cover for receiver signatures

For unrestricted binary monotone circuits computing threshold two, let E=C(n)−2n−√(2n). We prove

    liminf E/n^(3/10) ≥ √(5/8).

We use the unrestricted receiver graph and the component cancellation in unrestricted-coefficient-final.md. Along a regular sequence with bounded normalized excess, put t=√(2n), h∼t, K∼hE, E=Θ(h^(3/5)). Let H be the high shared antichain, with L missing pairs on H, z=L/(hE)≤1+o(1). There are g∼h selected groups, each missing only o(h) shared raw neighbors, uniformly. They are the edges of the simple receiver graph on w≤(3+z+o(1))E vertices; pairwise disjoint edges with identical four-vertex unions cannot both represent an actual raw. The groups of H are all distinct from these receiver columns.

## Removing rows with two private columns

A private receiver of a selected group cannot be the circuit output, since a singleton incident to the selected group would then be accepted. Hence it feeds a single AND pin. Among selected rows having both columns private, at most a=O(E) rows have their two columns on the same AND (the pair of columns uniquely identifies a row). For the rest independently select one pin of every AND with probability one half for each side. Each remaining row has probability one quarter of having both its private pins selected. There exists a choice retaining at least a quarter of them.

At most one actual raw can join two of the retained rows. Otherwise turn on two such distinct raws. Every directly activated selected group feeds only the private receiver columns attached to chosen pins. No AND can be first to turn on: prior to any active AND the only groups that can fire are those directly activated and their private OR receivers, and none of the ANDs sees two true pins. The output cannot be one of these groups by singleton rejection. Thus two active raws would be rejected. As every absent pair inside the selected set counts in L, the number of these two-private rows is O(√(L+1)+a)=o(h). Delete them, then repeatedly remove any vertex of degree zero or one. This further discards at most w edges. The remaining graph still has g'∼h edges, every edge meets a shared column, and every nonisolated column has degree at least two.

## Almost every high probe misses each surviving column

For any remaining column W, take an edge C=(W,P) and another edge A at P. For any B∈H distinct from A,C, suppose both AB and CB are actual raw edges and the B-probe activates W. On singleton AB the receiver P is already true through A and W through B. Adding the raw CB cannot change the output, since B is already true and both receivers of C are true. This contradicts correctness. The two selected groups A,C miss only o(h) shared raw neighbors, uniformly. Therefore at most o(h) probes from H activate W.

If W is shared, it has only o(h) raw neighbors in H by the common-neighbor obstruction, and is outside H. It succeeds at least one selected group, so cannot precede any group in the antichain H. Consequently at least h−o(h) pairs between W and H are incomparable missing pairs. Distinct shared columns charge distinct pairs outside H×H. Writing u for the number of remaining shared receiver columns gives

    u ≤ (q−L)/(h−o(h)) ≤ (1−z+o(1))E.

## The two-class degree bound

Pass to any subsequence on which z has limit z₀∈[0,1]. Let ε>0 be fixed and small. Pad only with isolated private vertices. The actual total is at most W₀=(3+z₀+ε)E. For an honest enclosure, first pad only the private class so the total is ceil(W₀), retaining the actual shared size u. Its order is u≤(1−z₀+ε)E≤W₀/2 for ε small. The product u(W₀−u) is bounded above by (1−z₀+ε)(2+2z₀+O(ε))E². This procedure needs no assumption on the actual private count.

Let G=g' be the remaining edge count. All edges meet the u shared vertices. Among graphs with these class sizes, the shared degree sum is at least G and the total degree sum is 2G. By classwise Cauchy–Schwarz and u≤W₀/2, the sum of squares of degrees is at least G²(1/u+1/(W₀−u)), since the unconstrained degree-proportional minimum has shared degree sum at most G. Thus the codegree sum T over unordered vertex pairs is at least G²W₀/[2u(W₀−u)]−G.

The nonedge moment argument used in matching-codegree-constant.md gives L≥(1−o(1))T²/(2W₀²). For clarity, T≥Ω(G²/W₀), L=O(h^(8/5)), and the sum of squared codegrees is at most T+6L by the four-cycle collision bound. Adjacent pairs contribute at most √(G(T+6L))=o(T). Apply Cauchy–Schwarz over at most W₀²/2 nonadjacent pairs and subtract the linear term, which is negligible since T≫W₀². Each four-set contributes at most twice its forced missing matching count to the resulting sum of binomial codegrees, proving the inequality. Isolated padding changes none of the codegrees that are positive.

It follows that z₀ cannot equal zero or one along a bounded normalized-excess sequence, by the following common inequality and then ε→0:

    (z₀+o(1))(1−z₀+ε)²(2+2z₀+O(ε))² E⁵ ≥ (1−o(1))h³/8.

The maximum of z(1−z²)² on [0,1] is 16/(25√5), attained at z=1/√5. Consequently E⁵/h³ has liminf at least 25√5/512. The regular-or-delete transfer preserves the coefficient, and 2^(3/10)(25√5/512)^(1/5)=√(5/8).
