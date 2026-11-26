# Opposite-side leaf budgets extend the incidence deletion bound through 322

Use the live-circuit antichain decomposition and the adaptive restriction recurrence in antichain.md. Write d for deletions, V=2N−d for the number of surviving vertices, and e for the residual circuit excess. At most 3e+1 surviving vertices are marked, and unmarked vertices have at most one neighbor outside their read-once component.

Consider the u unmarked vertices in one part and suppose a opposite vertices have been deleted. Those of degree at most two contribute at most 2 each to their residual degree sum. The others have internal degree at least two and hence are centers in the component star forests. Their internal leaf sets are disjoint and consist of opposite surviving vertices, so sum to at most N−a. Their external degrees sum to at most their count. Thus the total residual degree of all u is bounded by 2u+N−a.

The incidence count L from these vertices to opposite deletions satisfies L≥(q−1)u−(N−a). The second moment gives L²≤au(q+u). Also L²≥(q−1)²u²−2(q−1)u(N−a), including when the right-hand side is nonpositive. Therefore, for a<(q−1)²,

    u ≤ f(a) = [qa+2(q−1)(N−a)]/[(q−1)²−a].

Writing f(a)=(q−2)+C/[(q−1)²−a] gives C=2(q−1)N−(q−2)(q−1)²>0. By convexity f(a)+f(d−a)≤f(0)+f(d). Thus the residual has excess e≥ceil((V−floor(f(0)+f(d))−1)/3). The original circuit has s≥2N+d−1−floor(qd/(q²−d))+e.

Set d=q²−26q. The companion script check-sided.py verifies with rational arithmetic that Nq≤100s for every integer 289 through 322. At q=322 it gives s≥335447 and the target is 334903. The proof has received an independent mathematical review, but is not Lean-formalized. It uses only weight-two correctness and the previously established adaptive restriction lemma, so the method does not imply asymptotic superlinear lower bounds on prime-order planes.

For weaker sparse-mask promises, [a hashing construction](small-masks.md) yields small circuits over prime-order planes.
