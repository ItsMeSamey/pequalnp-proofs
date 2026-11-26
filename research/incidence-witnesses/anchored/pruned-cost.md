# Shared baselines and pruned path costs through order 396

Use the extraction rows and producer decomposition in README.md. Let G_P and G_L count extractable queries in the two polarities and G=G_P+G_L. Write s for original gates and compare the two separate extraction circuits' total costs.

Start with at most 2s original-gate evaluations for the two shared baselines. For each of the 2N essential input variables choose a gate that directly consumes it. That gate's copy in the baseline that sets this input to zero simplifies to zero (AND) or to the other argument (OR), so no gate is needed. Each chosen original gate can account for at most two distinct input variables, hence this saves at least N baseline gates. This only forwards simplified values; it does not alter inlets supplied to the contexts.

In a component using ordinary contexts, descend only into branches containing a requested query variable. An AND gate requires at most one new gate for the first such child and one more if both children lead to a requested leaf. A rooted tree pruned to g queried leaves has at most g−1 branching vertices when g>0. Thus the context cost is at most the original gate count of the component plus g. For components with just one query and locally zeroed data, the independent sibling subtrees and the conjunctions along the query path together cost at most the original gate count, as in README.md. Therefore total context cost for both polarities is at most 2s+G. Allow two shared constants per extraction circuit. Their total size is at most 4s+G+4−N.

Each row incurs at least q−1 distinct local gates within its polarity. Hence (q−2)G≤4s+4−N. The distinct nonoutput singleton producer argument gives 2N−G≤s−2N+1, or G≥4N−1−s. For q≥2 it follows that

    (q+2)s ≥ (4N−1)(q−2)+N−4.

The integer checks in check.py cover 3≤q≤396. At q=396 this gives at least 622926 gates versus the target 622564. For q=2 the basic essential-input lower bound suffices. Both the local context proof and this counting refinement received independent review.
