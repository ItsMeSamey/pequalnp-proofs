# Counting live ports by their sources and destinations

Use the components, definitions and antichain bound from first-side.md. Say that a node is R-live when it is positive on some R singleton. No component with an L vertex x adjacent to an external R vertex y can have an R-live exit. Indeed, an R singleton z making its exit one also makes it one in the presence of y. Outside that component the input z,y dominates the external variables of x,y, since x is local and y is external. Replacing the component's exit by the constant one on both assignments can only increase the x,y output and preserves the z,y output. Therefore z,y would be accepted despite comprising only R vertices (possibly a singleton when z=y).

Let p count the R-live producers and let E_R be the sum of their excess fanouts (fanout minus one). They emit p+E_R R-live port occurrences altogether. Of the p active-producer components, at most r can contain a local R variable, where r is the total number of surviving R variables. Each of the others has an R-live inlet, because it has an R-live exit and local R singleton activation cannot originate within it. Therefore at least p−r R-live ports terminate in components which have R-live exits and cannot have any marked L vertices. The marked components thus use at most E_R+r R-live ports in total. By the antichain bound, their marked count is at most that number plus the number of marked components having zero R-live ports.

Such a zero-live-port marked component must have an R-inactive exit by the first paragraph, and cannot be the overall output component: its marked singleton alone would activate the exit. Each consequently has a distinct inactive producer as its root and consumes at least one unit of e−E_R. It follows that the total number of marked L vertices satisfies

    M_L ≤ e+r.

# First-side deletion bound

Take d=q²−20q, 289≤q≤376. The room and cost accounting are as in first-side.md. At stopping, designate as L the side with h≤d deletions. Exactly r=N−d vertices of R survive and N−h vertices of L survive. The count u≤U=floor f(d) of unmarked surviving L vertices uses only d opposite deletions and r surviving R vertices. Hence e≥(N−h)−U−r=d−h−U. Also e≥0. Accounting for all cheap steps and final isolates by the original moment bound gives

    s ≥ 2N+d+h−1−floor g(d)−floor g(h)+max(0,d−h−U).

Put h0=d−U (positive throughout the stated range). For h≤h0 the right side is minimized at h0 because g increases. Above h0, h−floor g(h) is nondecreasing: for 0≤a≤b≤d the exact difference g(b)−g(a) is q³(b−a)/[(q²−b)(q²−a)]≤b−a since q≤400. Thus the bound for all h is

    s ≥ 2N+2d−1−U−floor g(d)−floor g(h0).

The integer check in routing-check.py verifies all orders 289..376 and checks that each deletion step has room. For q=376 this is 533233 gates against the target 532992.

# Asymptotic consequence

For q≥16 let t=ceil(sqrt(q)) and set d=q²−2qt. Then q²−d=2qt and (q−1)²−d=2q(t−1)+1. Hence g(d)≤q²/(2t), and N−d=q+1+2qt>g(d)+1, since t²≥q. In particular the same first-side stop is available. Also

    f(d) ≤ [q³+2q(q+1+2qt)]/[2q(t−1)] = O(q^(3/2)).

Using e≥d−h−floor f(d) and b≤2g(d) in the original cost estimate gives

    s ≥ 2N+2d−1−f(d)−2g(d)
      = 4N−[2(q+1+2qt)+1+f(d)+2g(d)]
      = 4N−O(q^(3/2)).

This uses only the bipartite graph on accepted pairs, including singleton and same-side rejections.

# One additional finite order

For q=377 keep both inequalities e≥d−h−U and 2e≥N−h−U, the latter from first-side.md. With d=134173, N=142507 and U=7892 the integer bound

    s ≥ 2N+d+h−1−floor g(d)−floor g(h)+max(0,d−h−U,ceil((N−h−U)/2))

is at least 537272 for every integer 0≤h≤d. The target is 537252. The final loop in routing-check.py verifies every h as well as availability of each step.

# A joint degree count for order 378

Set q=378 and d=q²−19q. Let b_L count cheap deletions plus surviving isolates on L, and retain the unmarked surviving L set U (size u). For x an original L vertex let k be its number of neighbors among the r=N−d surviving R vertices, including when x was deleted earlier. Let c(k)=k−1 for k≥3, and zero otherwise. The total of c(k) on U is at most r: every unmarked degree-≥3 vertex has internal degree ≥k−1, and the opposite leaves of these stars are disjoint. Vertices counted in b_L have k≤1. A vertex in both U and b_L must be a surviving isolate, hence has k=0.

For weights w=1,2 write Q_w(k)=(w+1)(k−20)(k−21)/420 and take a_1=4/65, a_2=2/35. Direct integer comparisons for each k from 0 to 379 establish

    Q_w(k) ≥ w·1[k≤1],
    Q_w(k)+a_w c(k) ≥ 1+w·1[k=0].

Use the second bound when x belongs to U, and the first otherwise. It follows that

    w b_L+u ≤ a_w r + sum_{all original L vertices x} Q_w(k_x).

Two distinct surviving R vertices share exactly one original L neighbor. (Distinct points have a unique common line by the plane axioms. Distinct lines meet in one point by the usual degree count from any point on the first line, or one can use ≤1 here since Q_w has positive quadratic coefficient.) Thus sum k=(q+1)r and sum k²≤qr+r². Evaluating gives b_L+u≤13355 and 2b_L+u≤19766. The original gate inequality, with e≥d−h−u and 2e≥N−h−u, therefore implies

    s ≥ 2N+d−1−floor g(h)+max(d−13355,ceil((N+h−19766)/2)).

The final loop of routing-check.py verifies these inequalities by integers and checks every h, yielding s≥542462 against the target 541535.

# Reserving source vertices for order 379

In the routing lemma let a count the R-live producer components having no R-live ports. Since the other p−a R-live producer components each consume a live port, the same routing proof gives M_L≤e+a. Each counted component has a local R variable whose singleton activates its exit. With all external inputs zero, the downstream circuit therefore rejects even when this exit is one, since that singleton is rejected. Hence its internal pair graph is empty. Reserve one such local R variable per component. Thus t=r−a bounds the total number of opposite leaves available to unmarked L centers: no center contributes leaves from a reserved component. The degree weights from the preceding section now satisfy sum_U c(k)≤t, while e≥N−h−u−a=d−h−u+t.

Set q=379, d=136977 and r=N−d. To see that every step remains available, use the sharper degree-zero estimate that at most qd/[(q+1)²−d] original vertices have no surviving opposite neighbor. Its proof is the ordinary degree moment with at least q+1 deleted neighbors rather than q. This estimate is below r. At every prefix the same upper bound applies since opposite deletions are at most d and at least r vertices of each part survive.

Put P=qr+r²−39(q+1)r+380N. For w=1,2 the quadratic (w+1)(k−19)(k−20)/380 and coefficient 1/15 satisfy the two pointwise inequalities in the degree-count argument for each allowed k. Consequently w b_L+u≤(w+1)P/380+t/15. In the two previously used excess bounds, this gives

    s ≥ 2N+2d−1−floor g(h)−2P/380+14t/15,
    2s ≥ 2[2N+d−1−floor g(h)]+N+h−3P/380−t/15.

For each integer h=0..d the first inequality under s≤T−1 yields an integer upper bound on t; substituting this in the second certifies s≥T. The exact integer verification in reserved.py proves s≥545926, exceeding the target 545840.
