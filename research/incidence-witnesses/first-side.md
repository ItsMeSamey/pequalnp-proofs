# One-sided high-degree bound

Use the producer-rooted read-once components and singleton antichain lemma proved in antichain.md. Fix one part L of the bipartite graph, and call the other part R. An input port is live for R if its wire ever evaluates to one on an R singleton. Count port occurrences, including all repeat uses. On testing (local singleton in L, external singleton in R), every nonlive port is zero, since no local variable can influence an incoming port. In component i fix the nonlive ports to zero in its read-once formula, and let t_i count the remaining ports. By the same antichain argument, the number m_i of local L variables with at least two external neighbors is at most max(1,t_i). Outside means outside the component; bipartiteness ensures the neighbors belong to R.

If t_i=0 and m_i>0, some local x of part L must activate the root by itself, since otherwise x cannot change the result on any external R singleton. No external R singleton can itself activate this root: all ports are zero and every monotone AND/OR node is zero when all its inputs are zero. No local singleton z of part R can activate it either. If it did, choose an external neighbor y of x. On the two pairs x,y and z,y the group root is one (all relevant inlets are zero in both cases), and everything downstream sees the same value and the same external input. This would accept z,y in a single part. Therefore this root is R-inactive. The overall output component cannot be such a component because the singleton x would be accepted. Every other component's root is the producer of at least two ports, one retained use and one or more duplicate uses. Thus if k counts components with t_i=0 and m_i>0 then at least 2k of the ≤2e total port occurrences are R-inactive. Consequently

    M_L = sum_i m_i ≤ sum_i t_i + k ≤ 2e−k ≤ 2e.

# Stop on the first side reaching d deletions

Set d=q²−24q. Perform the usual zero-restriction elimination steps until either part first reaches d deletions. If a prefix has x≤d opposite deletions then at most g(x)=qx/(q²−x) original vertices on this side have at most one residual neighbor, by the ordinary Cauchy packing bound. At least N−d>g(d)+1 vertices remain on each side throughout the stated finite range, so an edge is available and there is a next step whenever required. The process stops after at most 2d−1 steps. At stopping write h≤d for the deletion count on the other side and designate its still-larger surviving vertex class as L. Let b be cheap deletions plus remaining isolates. Monotonicity of depleted status implies b≤floor(g(d))+floor(g(h)) as before. The original size satisfies

    s ≥ 2N+d+h−1−b+e,

where e is the residual excess relative to its actual occurring variables.

There are N−h remaining L vertices. Let u count the L vertices with at most one outgoing neighbor external to their read-once component, adding all unrepresented isolates to u. Then N−h−u≤2e by the preceding lemma. Their total residual degree is at most 2u+r, where r=N−d is the opposite live vertex count: any unmarked vertex of degree ≥3 has internal degree ≥2 and therefore is the center of an internal star. The sets of opposite leaves of these L centers are disjoint and total at most r. Thus their incidences into d deleted opposite vertices total at least (q−1)u−r. As in antichain.md, second-moment packing then gives

    u ≤ f(d) = [qd+2(q−1)(N−d)]/[(q−1)²−d].

Taking integer floors, the initial size obeys s≥2N+d−1−floor(g(d))+(N−floor(f(d)))/2 + h/2−floor(g(h)). The final two terms give a nonnegative correction since q²−h≥24q. The integer arithmetic in check-first-side.py verifies all q=289..336.
