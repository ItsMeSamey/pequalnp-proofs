# An explicit unrestricted coefficient by component cancellation

Write t=√(2n), s=C(n)−2n and E=s−t. For minimum unrestricted-fanout binary monotone AND/OR size of threshold two,

    liminf E/n^(3/10) ≥ 2^(3/10)(2/4⁴)^(1/5) = 2^(−11/10).

The coefficient equals approximately 0.466516. The proof supplements unrestricted-matching-exponent.md and uses its notation. Along regular sequences with finite normalized liminf, E=Θ(t^(3/5)), K∼hE, h∼t, a=O(E), l=O(E), M=O(hE), and q≤K. The full raw graph has one giant component containing the antichain H of shared-degree >h/2 groups, and c₀=O(E) components in all. In particular the number of private OR groups including zero-raw receivers is at most 2a+1=O(E), since each ends at an AND pin or the output. So the number b_U of private raw neighbors of any shared group is O(E). The star flow bound gives J_U=D_U−q_U=d+3+t_U−b_U≥0 with Σ J_U≤K−q (subtract twice the incomparable missing pairs from the degree-deficit sum). Here d=s+1−h and q_U counts incomparable missing pairs at U. Summing shows d≤(K/h)+O(E)=O(E).

Let v=|H|=h−O(E). Let L be the number of missing pairs within H, and put z=L/(hE), so 0≤z≤1+o(1). All groups outside H together number at most l+2a+1=O(E). The edges avoiding H thus number O(E²)=o(hE). Summing degrees gives

    (Σ_{X∈H} k_X)/v = [n+binom(v,2)−L−O(E²)]/v ≥ t−L/h−o(E).

Select a set G of g∼h groups as in the unrestricted receiver-graph proof, additionally requiring their shared degrees to be at least (1−ε_h)h for ε_h→0. Such a choice exists by the missing-pair bound. Let w count the receiver columns of the g-edge graph. Each receiver W, even if private, has o(h) raw neighbors in H uniformly. Indeed a selected B feeding W has (1−o(1))h shared neighbors, and any common raw neighbor X of B and W would make the raw WX invisible when added to singleton BX. Every receiver lies outside H.

## Two OR savings at an accessible remote anchor

Call a remote component accessible if it contains a receiver of G; write b for the number of other remote components. For each accessible component fix a receiver W fed by a selected B and an actual raw edge WV. For all but o(h) centers X∈H there is an actual raw XB, uniformly in B. Say this component is usable for that X; denote the number of inaccessible-to-X exceptions among the accessible components by r_X. Then Σ_{X∈H} r_X/v=o(E), as c₀=O(E).

Apply the physical component/star OR proof of threshold-lower.md with center X of degree k_X (the proof works for any center of degree at least two). In its formal circuit each raw-bearing group W is given its own formal pin, replacing the disjunction of its raw inputs. Before any restrictions, parenthesize every usable anchor W as Wformal∨T, where T joins its nonraw operands. This arrangement costs the original number of ORs; T includes the incoming wire from B. As in the original proof, peel the giant tree around X and peel each remote component down to its anchor edge, assigning peeled pins zero. Use only constant propagation, retaining all nonconstant gates even if some later become unused.

For a usable remote anchor WV, all formal pins needed for singleton XB and for its union with raw WV are still available: X and B are in the retained star and W and V are unpeeled. On singleton XB the group B is true, hence T is true with both Wformal and Vformal zero. On adding WV only the two formal pins of W and V could change; setting Wformal alone true changes no signal outside W since T already holds. Thus Vformal is essential (possibly with Wformal set true). Setting Vformal false saves at least one OR by the original essential-pin argument: follow a live path through initial ANDs to its first OR. An AND-only path to the output would make the residual identically zero, yet the retained star still has positive assignments. Throughout this step the reserved root Wformal∨T survives zero-constant propagation: Wformal remains an unassigned independent formal pin and T is true on the still available singleton XB and false on all-zero inputs. In particular the OR saved for V was not this reserved gate. Setting Wformal false now saves that second OR. Positive witnesses used for other components remain available with both pins zero.

The original count saved at least one OR per remote anchor pair; a usable pair saves two. The original inequality k_X≤s−a+c₀+4 therefore sharpens to

    k_X ≤ s−a+5+b+r_X.

Averaging over X and using the displayed degree lower bound gives

    a ≤ E+L/h+b+o(E).

## Counting receiver slots

Let N_ext denote the number of raw edges from H to its exterior. Since t−v=O(E),

    N_ext = n−binom(v,2)+L−O(E²) = h(t−v)+L+o(hE).

Among the at most l+2a+1 outside groups, each of the w receivers has o(h) raw neighbors in H, contributing o(hE) in total since w=O(E). Each of the b remote components containing no receiver supplies at least two additional distinct nonreceiver groups with no raw neighbor in H. The other groups contribute at most h raw neighbors apiece. Hence

    w ≤ l+2a−(t−v)−L/h−2b+o(E)
      = 2a+E−d−L/h−2b+o(E)
      ≤ (3+z)E−d+o(E).

The nonedge codegree bound in matching-codegree-constant.md applies directly to the unrestricted receiver graph: every missing matching pair among G occurs within H, so it counts toward L. The bounds g∼h, w=O(h^(3/5)), L=O(h^(8/5)) imply L≥(2−o(1))h⁴/w⁴, exactly by its two codegree moment estimates. Therefore z(3+z+o(1))⁴ E⁵≥(2−o(1))h³. The maximum of z(3+z)⁴ over 0≤z≤1 is 4⁴. Using t^(3/5)=2^(3/10)n^(3/10) and the regular-or-delete transfer of unrestricted-matching-exponent.md proves the claim.

The earlier slot inequality also records a specific gap to the matching-layer coefficient: w≤E−L/h+2(a−b)−d+o(E). If 2(a−b)−d≤o(E) on a near-optimal sequence, this recovers the matching-layer tradeoff w+L/h≤E+o(E). An unrestricted proof of that additional premise is not known here.
