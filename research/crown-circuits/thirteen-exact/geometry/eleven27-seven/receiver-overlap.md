# Singleton overlap at a flag reader

Use the simple 13-edge incidence host for a minimum regular size-31 threshold-two circuit with seven AND gates. On raw inputs a flag X is the disjunction of its incident labels. Consider a decoder gate with operands X and P, or an OR group with X a direct operand and P the disjunction of the rest. If at least one incident label activates P on its singleton, at least three incident labels must fail to activate P on their singleton.

Suppose there are only r≤2 exceptions and erase them. X retains a label. Every remaining assignment with X true contains a singleton activating P, so P is true by monotonicity. This works even if P has an earlier dependence on X. The reader folds to P for an OR or X for an AND. In an OR group associate to add X last.

The residual bank saves 2r−l ORs, where l flags are newly isolated. All l are distinct degree-one neighbors of X since the erased edges form a star, the host is simple, and X retains a label. They are mixed flags with distinct dedicated decoder ORs, saving l further ORs. These differ from the folding gate. If the group has another mixed raw flag Z, associate Z with a different operand inside P before adding X. If P=Z, the retained overlap keeps Z live. Thus 2r+1 gates disappear, contradicting minimality when r=0 and the known 29- and 27-gate minima at r=1 and 2.

Every at-most-three-label flag therefore has disjoint singleton support from the rest of its OR group. A quartet shares at most one label. Adjacent pure triples cannot feed one OR group. For an AND the statement concerns its two operands only.

A mixed group has zero overlap at every degree: a direct raw leaf activating an earlier nonraw operand on its singleton implies that operand on every input, so removing the leaf saves a gate. A branching pure quartet cannot have the same redundant label in both its OR readers: remove that label from the shared pure tree and each reader retains its original value in topological order, provided its other operands already cover the singleton.
