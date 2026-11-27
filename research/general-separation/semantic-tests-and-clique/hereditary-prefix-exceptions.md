# Exact hitting sets for tries with bounded prefix exceptions

Let A be a nonempty subset of the binary strings of length m. A prefix is viable if at least one of its extensions lies in A. A viable internal prefix is exceptional if exactly one child is viable and that child's subtree omits at least one leaf. Let C(m,k), for k≥0, consist of the sets A for which every path to a member contains at most k exceptional prefixes. The exact size of a set meeting every member of C(m,k) is

    h(m,k) = Σ_{j=0}^{min(m,k+1)} binom(m,j).

At k=0 these are precisely the nonempty tries in which every viable prefix, including the root, contains at least half its descendant leaves. Indeed, half density at a unary viable node forces its child to be full. Conversely, with no exceptions, a full unary child guarantees half density at its parent, and two half-dense viable children together give half density at their parent. Induct upwards from the leaves.

## Proof of the hitting number

The strings of weight at most k+1 meet every allowed set. Follow the lexicographically first member. Each one on this path means that the zero child was unavailable. If the one child is full, the remaining lexicographically first suffix is all zeros. Every one before the last one therefore traverses an exceptional prefix. At most k+1 ones can occur.

For the reverse bound let T be any hitting set and split its marked leaves between the two child tries. At least one child portion hits C(m−1,k). Otherwise take avoiding sets from both children and join them under the root. Both children would be viable, so the root would add no exception. For k≥1 each child portion also hits C(m−1,k−1), since an avoiding set can be placed inside that child alone at a cost of at most one new exception. For k=0 each child needs at least one mark, since its full subtree can stand alone. Consequently h(m,k) is at least h(m−1,k)+h(m−1,k−1) when k≥1, and at least h(m−1,0)+1 when k=0. The depth-zero value is one for all k. Pascal's identity yields the stated lower bound, including the regime where the hitting set contains all leaves.

## Exact counting at zero exceptions

Given an n-variable Boolean formula Φ, put the bit b last in the row order and accept (u,b) when NOT (Φ(u) AND b). Every prefix above the b query has both children viable because b=0 always accepts. At the last query, a lone viable child is a full leaf. Thus the set is nonempty and has zero exceptions. Its cardinality is 2^{n+1} minus the number of satisfying assignments of Φ. One exact count and one subtraction recover #SAT. This proves #P-hardness under polynomial-time metric reductions for polynomial-time evaluable row predicates, already at k=0. On these inputs membership of any specified row remains polynomial-time decidable. The final position of b is part of the reduction.

The [checker](hereditary_exceptions_check.py) enumerates every nonempty set through depth four and obtains the exact hitting numbers by subset minimization. At m=4 the values for k=0 through 4 are 5, 11, 15, 16 and 16. It also verifies the count identity and zero-exception promise for every Boolean table on at most three variables.
