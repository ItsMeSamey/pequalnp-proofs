# Shared pure AND gates at rectangle-filter interfaces

Use the small zero-certificate selection in threshold-rectangle-supergraph-obstruction.md. Its selected union of products has, after deleting at most bm vertices, exactly the induced true singleton incidence graph H with edge count at least (q+1)(N−bm). This selection allows arbitrary shared pure monotone preprocessing on either shore. Fix the deleted raws to zero.

For each physical query AND j let S_j be its surviving singleton line support. Let X_j be the union of singleton point supports of opposite factors in selected products whose query factor is reachable from j by an OR-only suffix, including a length-zero suffix. The rectangle X_j × S_j lies in H because membership at j suffices for every reached query factor. H is four-cycle-free of maximum degree q+1, so that single rectangle contains at most q+1 edges, regardless of how many routes or products use j. Replace all query ANDs by zero. Every lost pair belonged to an accepting product that loses its line factor on this singleton. At each OR follow an originally high, now zero operand; this reaches a replaced AND and proves the pair falls in the associated rectangle. Thus at most (q+1)t_L edges are lost if t_L such interface gates occur. Repeat on the point side; the intermediate relation remains a subgraph of H, so at most (q+1)t_P further edges are lost. Only physical ANDs with an OR-only suffix to a selected factor count.

The exact reverse bound for two pure OR sides gives at least one original physical gate per surviving edge. Consequently

    s+q(t_P+t_L) ≥ (q+1)(N−bm).

This uses the recovered slot for each charged AND as well: the OR-only remainder has size at most s−t_P−t_L after all pure ANDs are removed.

An alternative retains arbitrary normalized point preprocessing and strips only the query ANDs. If t_L+bm≤(1−c)N for some fixed c>0, the surviving relation has at least cN(q+1) edges. Its reversed OR readouts have that total singleton support, giving Ω(Nq/log²q) by threshold-point-and-filter-lower.md.

For many query ANDs one can instead partition surviving lines into K classes on which the operands of each relevant query AND have comparable singleton supports. Forward the smaller parent on each class. Topological induction preserves every original query singleton evaluation there. Reverse each resulting query OR network separately with the normalized point side. These circuits have combined size ≤Ks and total output star size |E(H)|; all point singleton fractional covers are O(log q), giving s=Ω(Nq/(K log²q)) if bm=o(N). Separate by a color of the graph joining lines that demand opposite parent orientations at some AND. At most 2^t colors are needed for t relevant ANDs by recording one permitted orientation per line per AND. No small-K assumption follows for general circuits.
