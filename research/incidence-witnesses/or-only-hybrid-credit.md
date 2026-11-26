# Extra OR credits in the narrow/broad collision extraction

Use singleton line queries and point payloads on the original sparse-line promise. The line-star multioutput requires Nq ORs alone: for each line trace its rejecting full complement through both inputs of an OR and one rejecting input of an AND. All reached singleton supports lie inside the line; its q+1 points demand at least q branching ORs with support at least two, unique to this line. This uses an unrestricted point payload. A full complement of data lines need not be an admissible negative in the opposite orientation.

Let H contain the input ancestry of all narrow collision ANDs of query scope at most d, with h internal gates and v=s−h exterior gates. There are b distinct H boundaries and e distinct raw queries used directly in the exterior, with b≤min(h,v+1−e). Let r=2χ+1 be the number of pooled reverse passes including the scalar root; let a_l count broad jumps repeating label l. Assume d≥2.

Count only OR gates. The baseline costs at most s−N by the all-query-zero pure-component argument. Each exterior pass needs at most v+1−b−e merge ORs; the terminal insertions cost at most db join ORs. Reverse path transmission and data products are ANDs. All broad contributions on a given l need at most a_l² joins: if all a_l occurrences are ordered, the i-th sends at most 2(a_l−i)+1 contributions to future parent rows and the final output. Directly averaging the two sides of b≤min(h,v+1−e) gives, by maximizing the affine bound at h=(s+1−e)/2,

    s−N + d(χ+1)(s+1−e) + Σ_l a_l².

Indeed the two slopes before and after the crossing are d+r(d−2) and d(1−r). The last root pass needs one fewer OR for every label absent from the e direct raw inputs: all N output groups have at least one term by their incident singleton tests. This subtracts N−e.

The H cache and boundary joins give a further (d−1)(N−e) saving. Let C be the H gates with a syntactically query-only parent, including such raw inputs. Every specialized copy of such a gate folds against a constant. A purely-query H boundary with scope size j contributes at most j rather than d joins per pass. Consider undirected components of purely-query H gates and their raw inlets. Include isolated raws that enter mixed H gates directly. Each component with n raw sites and t pure gates satisfies t≥n−1 by connectedness and the bound of 2t on its edges. If it feeds a mixed H gate, that gate has a unique pure parent and hence pays for this component only, giving at least n gates of C in total. Otherwise there is a pure boundary in the component. For n≥d the t gates already save d(n−1)≥(d−1)n. For n<d its boundary scope has size at most n, saving a further d−n beyond the cache. This gives at least (d−1)n again. The components include all N−e queries that have no direct exterior use, and the credited joins were budgeted in every pass. Only one pass's savings are needed.

Consequently

    Nq ≤ s+d(χ+1)(s+1)−(d+1)N+Σ_l a_l²−dχe.

At χ=0, q=401 and s≤646424, the right hand side with d=132 is 64534525, below Nq=64642403. Thus in this orientation the full collision scopes cannot all have size at most 132. No upper bound on the number of broad jumps follows without the color and label-overlap hypotheses.
