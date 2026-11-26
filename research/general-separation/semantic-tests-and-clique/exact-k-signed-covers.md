# Counting directed covers with a prescribed number of cycles

Let a nonempty directed multigraph have N vertices, m labeled arcs, and s=N+m+2. Write H_k for the number of spanning arc subsets with indegree and outdegree one and precisely k directed cycles, including loops. H_k=0 outside 1≤k≤N. For 1≤k≤√s, the integer signed network computes H_k in polynomial space and time

    poly(s) · 2^{O(s log(k+1)/√log s)}.

This uses the [October 25 Boolean tensor contraction theorem](https://github.com/openai/math/blob/92b516ef8e/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-reduction.tex#L15-L48). In particular fixed k has the same rate as one cycle. When log(k+1)=o(√log s), the bound is subexponential in s.

Use the [directed signed network](directed-signed-rectangle.md), retaining exactly one incoming and outgoing arc per vertex and the signed mark carried by a selected arc. Remove the fixed root constraint. Assign every selected arc a color in [k] and force color constancy at vertices by comparing the colors of their selected incoming and outgoing arcs. Unused arcs carry a unique dummy code. Stream states for partially scanned incidence runs now hold the selected color as well as the mark. Each vertex has precisely one cycle color.

At the end of each vertex run in the outgoing stream, process that vertex's color. A k-bit register records previously encountered colors, starts empty, and must end full. An unseen color must be the least color still unseen. At its first vertex require the outgoing arc to be unmarked. Add that color to the register. A repeated color has no mark restriction at this step. Pass the register only between adjacent outgoing chunks. Runs spanning chunks are processed exactly once, in increasing vertex order. All register values are uniquely determined.

Fix a cycle cover and a valid coloring. Its k first vertices of distinct colors lie on k distinct cycles. Markings are unions of cycles avoiding those first vertices. As in the original construction the single global restricted-permutation sign, multiplied by the marked-vertex sign, contributes minus one per marked cycle. If the cover has c cycles, the sum over marks equals zero for c>k and one for c=k; c<k permits no valid coloring. For c=k there is exactly one valid coloring: number cycles in order of their least vertices. This proves the asserted count with no division and no enumeration of anchors.

For g=ceil(m^{1/3}) chunks per stream, ignoring immediate zero cases with missing incidences, color data costs O((m+N)log(k+1)) wires and register transfers cost O(gk). A chunk's degree is O((m/g+1)log(k+1)+g+k); the bundle sign tensor has degree O(g²). For k≤√s the wire budget is O(s log(k+1)), and the maximum degree is beneath the source exponent 9/10 for sufficiently large s. The table computations are polynomial in s and the final count is at most 2^m, so precision m+1 bits suffices. Splitting directed wires by equality tensors preserves the count and supplies the required bipartition.

## A limit for arbitrary orbit counts across a cut

Join a left bijection σ on b strands to a right inverse bijection τ⁻¹ by identifying the output labels. The number of directed circuits in the resulting two-sided permutation is the number of cycles of τ⁻¹σ. Exactly b cycles occur if and only if σ=τ. The matrix indexed by the two independently chosen permutations is therefore an identity matrix of order b!. It has rank b! over every field. A binary sum-product interface of h wires provides at most 2^h rank-one terms, requiring h≥log₂(b!). This obstruction concerns a specified interface with arbitrary bijections. It gives no unrestricted lower bound on algorithms for exact cycle counts.

The [finite checker](exact_k_signed_check.py) compares the cancellation counts with independent cycle enumeration, checks chunk state transitions, and tests the identity matrices through five strands.
