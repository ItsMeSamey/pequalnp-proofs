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
