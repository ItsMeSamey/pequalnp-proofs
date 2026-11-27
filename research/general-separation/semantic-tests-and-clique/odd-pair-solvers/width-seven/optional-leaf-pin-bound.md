# Optional leaves in a minimal induced all-odd support

Let H be a finite simple graph in which every vertex has odd degree. Let Z be a set of compulsory vertices and suppose no proper induced subgraph containing Z has all degrees odd. Then the number of degree-one vertices outside Z is at most |Z|. Degrees here are taken in H. There is no upper bound assumption on host degrees.

Write L for the degree-one vertices outside Z. No two elements of L are adjacent, because then their isolated edge could be deleted. No two share a parent, because deleting both would change their parent's degree by two and leave all other remaining degrees unchanged. Consequently their neighbors form a set P disjoint from L with |P|=|L|, each parent having a unique paired optional leaf. Put R=V(H)∖(P∪L).

Over the binary field solve for deletion indicators d_R,d_P subject to

    A[R,R] d_R + A[R,P] d_P = 0,
    d_z = 0 for z in Z.

The equations are homogeneous. There are |R|+|P| unknowns and at most |R|+|Z| equations. If |L|>|Z| they admit a nonzero solution. For each paired leaf set its deletion bit to one when its parent is deleted. For every retained parent instead set its leaf's deletion bit equal to the parity of the deletions among its other neighbors. Those other neighbors all lie in R∪P, so these choices are independent. Each retained parent loses an even number of neighbors. Each retained vertex in R loses an even number by its equation, and each retained leaf still has its unique neighbor. The result is a proper induced all-odd subgraph containing Z, a contradiction. Binary elimination constructs the smaller witness.

The bound is attained with two pins. Join two degree-three centers by an edge and give each center two leaves, one pinned. In any witness both centers must be selected to support the pinned leaves. Each center already sees its opposite center and its pinned leaf, so its remaining leaf must also be selected. Thus the entire six-vertex graph is forced and has two optional leaves.
