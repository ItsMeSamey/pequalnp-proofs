# Fixed OR excess forces nearly n ANDs in single-level threshold-two circuits

Consider binary AND/OR circuits with arbitrary fanout computing ordinary threshold two on n≥2 inputs. Single-level means that no input-to-output path contains two ANDs. If O and a are the OR and AND counts, then

    e = O − 2n + 4 ≥ 0,                 a ≥ n − 1 − e(e+1)/2.

In particular O≤2n−3 forces a≥n−2, attained for every n≥4. Four labels can be identified with the two-bit strings: compute whether both bit values occur in either coordinate with four ORs for the two sign groups of each coordinate, two ANDs, and one final OR. To increase arity by one replace one raw by the OR of two new raws and adjoin their AND to the output by one OR. Each split adds two ORs and one AND while keeping the circuit single-level.

## Transposing the OR front

Delete unused gates, constants and redundant gates, taking clean singleton rejection and all-pair acceptance as the characterization of threshold two. If these simplifications save gates it suffices to prove the asserted bound for the simplified counts, since the bound is monotone in each count over e≥0. Collect the AND outputs with a−1 ORs. A raw cannot feed the output through ORs alone. Consequently the rest of the circuit is an OR diagram from n raw variables to the two signed input pins at each of a AND comparators. The receiver mask of a raw is the set of pins reached from that raw via ORs. Each mask is consistent, meaning it contains no opposite signs of a common axis. Every two distinct raw masks conflict, meaning some axis occurs with opposite signs in the two masks. Thus they are incomparable. Both signs of each retained axis occur.

A one-pin receiver x can be deleted with at least two ORs and one AND saved when n≥4. Its pin is reached by no other raw (otherwise adjoining x to that other singleton makes no difference), so the pin computes x. The opposite comparator operand equals the full OR of every other raw, since pairs involving x need this comparator. It is independent of x. Delete x, its comparator and its collector OR. The opposite root is a distinct OR since n−1≥2. In the reduced circuit this root dominates all wires: its AND uses copy the other operand and its OR uses propagate the maximum. The residual threshold differs from the maximum, so this OR root can also be eliminated. At n=2 the OR floor is zero and at least one AND is required. At n=3 both an OR lower bound of two and an AND lower bound of two hold: the AND bound follows since one axis supports at most two conflicting consistent masks. For the OR bound, the output collector already needs at least one OR, and without a front OR every comparator has two raw operands, requiring three different comparators and therefore two collector ORs. These bases satisfy the stated inequalities.

Henceforth assume no one-pin receiver. Transpose the OR diagram. For an OR diagram with p live input wires, q designated output pins, and b binary gates, the reverse diagram realizes the dependency masks with at most b+q−p binary unions. At each original raw or gate with f≥1 outgoing occurrences (including output taps) join the f incoming reversed wires with f−1 unions, summing the degrees. Initially the bank contains both signed literals of each axis. The reverse budget is at most (O−a+1)+2a−n. Each of the n distinct nonliteral receivers needs its own last join, and none can feed a different receiver by incomparability. Reserve these n final joins. What remains is a bank with

    h ≤ a+e−3

helper joins. All used helper masks are consistent, being subsets of actual receiver masks.

## Components and palettes

Initially each axis is its own component. For a new helper join merge its operands' components if distinct. Every bank wire belongs to one resulting component. Write c for the final component count. In component i with tᵢ axes, exactly tᵢ−1 helper gates were such merges. If δᵢ denotes the number of the other helpers there, then Σδᵢ=h−a+c≤c+e−3.

Each component's bank wires have a proper coloring with 2+δᵢ colors for incompatibility. For a fresh axis color its opposite signs differently. On joining distinct components permute and align their palettes so the two operands share a color. Assign the helper that color. Wires in different components could not conflict, so the new color class is consistent. For an internal helper one new color suffices. Every color class is jointly consistent since its union contains no opposite signs.

Two simple counting facts will be used repeatedly. First, a designated output formed from an operand in component i and one in distinct component j is identified within this class by its pair of colors: two outputs with the same color pair cannot conflict. Second, after projecting onto t' retained axes, the number of surviving helpers from an original component is at most t'−1+δᵢ if t'≥1 and zero if t'=0. In its binary tree of component merges, a merging helper survives only if both original child subtrees retain at least one axis; there are at most t'−1 such branch vertices. The δᵢ internal helpers add at most δᵢ. Empty operands and aliases are bypassed.

Finally, if N≥2 remaining receiver masks stay pairwise conflicting after projection, discard every axis on which both signs do not occur among these outputs. This keeps all conflicts, so every receiver is nonempty, and there are t'≥1 effective axes. Given a projected helper/final-join realization with b joins, transposing back and using t' comparators with collector t'−1 gives a single-level threshold-two circuit on N labels with at most

    b+N−t'−1 ORs.

Both signs of every retained axis are live and trimming can only improve the bound.

## The OR floor

Assume a negative e, minimizing n. One-pin deletion reduces n at the same or lower excess, contradiction. Otherwise the helper count gives c≥4. Each raw uses one or two bank components and every two raw supports meet. Such sets share a common component or are the three edges of a triangle: in the absence of a singleton, two intersecting edges force an edge avoiding their common vertex to be the edge on their other two endpoints. Every component is used, because all signs occur. Thus c≥4 forces a common center. The l=c−1 leaves each need at least one center color distinct from all other leaves' choices: raw outputs at different leaves can conflict only in the center. But its palette has at most 2+δ₀≤c+e−1<l colors. Contradiction.

## The AND count

Set f(e)=1+e(e+1)/2 and argue by contradiction, minimizing lexicographically (e,n,a) among circuits violating a≥n−f(e). One-pin deletion contradicts minimality since it saves one AND, one label and at least two ORs. It therefore suffices to examine the helper bank.

**One component.** Here δ=h−a+1≤e−2 and e≥2. If there is no helper then a=1, which cannot support more than two labels. Otherwise remove the last helper H and the d final receivers using it. It was live and d≥1. The other operands of these receivers are pairwise conflicting: each is individually compatible with H, so neither can conflict with H in another output. Thus d≤2+δ≤e by the palette. If N=n−d≤1 then n≤e+1≤f(e), enough. Otherwise project the N surviving masks onto their effective axes.

If H was internal, the number of projected helpers is at most t'−1+δ−1. If H merged two components, their remaining internal excesses sum to δ. When both contain effective axes, at most t'−2+δ helpers survive. If just one contains effective axes, at most t'−1+δ survive, but at least one of the N receivers requires no final join. Indeed H contains a literal from the disappearing child. The opposite literal occurred in some original receiver because every sign is live, and this receiver could not have used H. Its operand carrying the opposite sign lies in the disappearing child since H was its only link to the other child. Projection deletes this operand, leaving a single bank wire as the output. In each case helpers plus final joins total at most t'−2+δ+N. Back-transposition gives an OR excess at most δ+1≤e−1. Minimality of e gives a≥t'≥N−f(e−1)≥n−f(e), since f(e)−f(e−1)=e≥d.

**Triangle.** If the supports have no common center then c=3 and all three classes AB, BC and CA occur. At each vertex the incident classes use disjoint sets of colors; two raws from different incident classes can conflict only at that vertex. Each of the six incident class ends uses one base color plus x≥0 additional colors, with the total of all six x's at most Σδᵢ≤e. Class size is at most the product of its two end counts. Summing the three bounds gives

    n ≤ 3+e+⌊e²/4⌋.

Indeed the sum of the three products of endpoint extras is at most ⌊e²/4⌋ by arbitrarily orienting each class edge and multiplying the sums of extras on its two sides. Since a≥3 and e+⌊e²/4⌋≤f(e), this suffices.

**Star.** Otherwise fix a common center 0 and l=c−1≥1 leaves. There are n₀ center-only raws; all other raws join a center wire to one leaf wire. In leaf i put qᵢ=δᵢ and retain the most populated leaf-color class of external raws, of size kᵢ≥1. Write uᵢ=kᵢ−1. Retain also all center-only raws, giving k=Σkᵢ and N=n₀+k. These outputs still conflict upon projection to the center, because all retained leaf operands at the same leaf are compatible; raws from different leaves were already forced to conflict at the center. The number removed at leaf i is at most (1+qᵢ)kᵢ since it had at most 2+qᵢ colors. Therefore the number removed minus the total leaf axes is at most

    Σ[(1+qᵢ)kᵢ−1] = Σ(qᵢ+uᵢ+qᵢuᵢ).

If N=1 then n₀=0, l=k=1 and the one leaf had at most 2+q₁≤e+1 raws (here c=2). This immediately suffices. Otherwise keep only the t' effective center axes. The retained external outputs already exist as bank wires, so there are at most t'−1+δ₀+n₀ projected joins. Back-transposition gives a circuit with OR excess e'≤δ₀+2−k. The OR floor ensures e'≥0. Thus r=e−e' satisfies

    r ≥ e−δ₀−2+k ≥ Σ(qᵢ+uᵢ),

using Σδᵢ≤l+e−2. The excess removed labels beyond leaf axes is at most r+⌊r²/4⌋. If r>0, use induction on excess in the smaller circuit and the elementary inequality

    f(e)−f(e−r) ≥ r(r+1)/2 ≥ r+⌊r²/4⌋.

This gives a≥n−f(e). If r=0 the removed labels do not outnumber the leaf axes. Induct on n if N<n, and on the number of ANDs if N=n, because at least one leaf axis has been discarded. This completes the proof.

This result concerns the single-level model. For a separate raw input to a dirty intermediate AND, a receiver may contain both formal signs of that comparator while still rejecting the singleton. The conflict-mask argument above consequently requires its stated scope.
