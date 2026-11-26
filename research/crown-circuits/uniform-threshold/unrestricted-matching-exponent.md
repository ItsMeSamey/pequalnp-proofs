# The unrestricted third-order exponent for monotone threshold two

For minimum fan-in-two monotone AND/OR size C(n) with unrestricted fanout, there are absolute positive constants c,C such that for all sufficiently large n,

    2n+√(2n)+c n^(3/10) ≤ C(n) ≤ 2n+√(2n)+C n^(3/10).

The upper bound is the construction of three-level-matching.md. The lower bound here uses shared-or-cut.md, the star-restriction telescope of star-third-order.md, and the component/star OR accounting of threshold-lower.md. No constant multiplying the third-order term is asserted sharp.

## A large antichain of shared groups

First take a regular global minimum of size 2n+s. Let t=√(2n) and E=1+max(0,s−t). It suffices to consider E≤t^(3/5) (a larger excess already proves the claimed order). The existing lower bound yields s≥t−O(1). Write h for the number of shared OR groups, d=s+1−h, and K=(s²+7s+14)/2−n. Then K=O(tE), d²≤2K, and h∼s∼t. In what follows all constant bounds are uniform as n grows.

Use the strict probe order U<W of shared-or-stability.md. Write p_U,t_U for numbers of strict predecessors and successors, k_U for total raw degree, m for the number of shared–shared raw edges, q for incomparable missing shared pairs and e≤4 for raw edges avoiding shared groups. Comparable pairs have no raw edge and cannot have a common raw neighbor: on the singleton UX with shared W activated by U alone, both X and W already hold, so adding WX would do nothing.

The enumerative identities and star-flow bounds give q≤K and D_U=s+3−p_U−k_U≥0 with Σ D_U≤2K, as derived in star-third-order-density.md. The star specialization yields k_U+t_U≤s+6. Consequently t_U−p_U≤D_U+3. In the comparability DAG, the number of all comparable pairs going from any downward closed ideal to its complement equals the ideal sum of t_U−p_U, at most B=2K+3h. In particular every prefix cut of a topological order has at most B pairs. Summing over prefixes bounds the sum of the lengths of comparable pairs by hB. There are at most hL pairs of length ≤L and at most hB/L longer pairs. Taking L=ceil(√B) shows there are O(h√B)=o(h²) comparable pairs, and including the q incomparable missing pairs leaves o(h²) missing raw pairs in all.

Let H consist of shared groups with degree greater than h/2 in the shared raw graph, and l=h−|H|. The preceding density gives l=o(h). Every two members of H have a common raw neighbor in the shared graph and therefore are probe-incomparable. The strict predecessors of elements of H form an ideal I disjoint from H. Also I∪H is an ideal. Every comparable pair from outside H into H crosses the cut of I, and every comparable pair from H to outside H crosses the cut of I∪H. Thus at most 2B comparable pairs touch H. There are at most binom(l,2) remaining comparable pairs. If M counts all missing shared raw pairs, then

    M ≤ q+2B+binom(l,2),       l(h/2−1) ≤ 2M.

Since l=o(h) these imply l=O(B/h)=O(E) and M=O(hE). In particular m=binom(h,2)−O(hE).

## The secondary receiver graph in an arbitrary circuit

Let Δ be the largest raw degree among all OR groups, a the AND count, and c₀ the number of connected components of the full simple raw graph, omitting groups with zero raw degree. Every member of H belongs to the same component since each pair has a common neighbor. Every other component either contains a shared group outside H or contains one of the e≤4 all-private edges, so c₀≤1+l+4=O(E). Summing raw degrees over the shared groups gives n−e+m, whence

    Δ ≥ (n−e+m)/h ≥ n/h+h/2−O(E) ≥ √(2n)−O(E).

The physical component/star OR bound from threshold-lower.md gives Δ≤s−a+c₀+4. Therefore a=O(E).

Keep the groups in H whose fanout is exactly two and whose two readers are ORs. Call their set G and its size g. At most d shared groups have fanout above two. At most 2a shared groups have an AND reader, so g∼h. Each group in G feeds two DISTINCT flattened OR receiver groups: were both occurrences in the same private OR tree, one could be deleted by idempotence, saving a gate in the original minimum. A receiver of U∈G cannot be in H, since an OR-only path U→W makes U<W. Thus each receiver is either one of the l shared groups outside H or a private group. Every private receiver group ends at an AND input or the circuit output, so the number w of possible receivers is at most l+2a+1=O(E).

Represent each U∈G by an edge between its two distinct receiver groups. These g edges form a simple graph R. Indeed two distinct U,V∈G have a common raw neighbor X. On the singleton UX the two receiver groups of U are true. If V had the same two receivers, adding VX could have no downstream effect: X is already true, while all paths out of V first reach one of its already-true receivers. This contradicts threshold two. This argument works with mixed OR groups; their private internal gates have no consumers outside their flattened group.

For each actual raw pair of endpoints A,B∈G, its singleton makes both A and B true, hence makes all vertices of the receiver union R(A)∪R(B) true. Two distinct actual raw pairs AB,CD cannot have the same union. Adding raw CD to singleton AB could then affect only the groups C,D and their private receiver paths up to already-true receiver groups, leaving the output unchanged. In particular two different perfect matchings of the same four vertices of R cannot both represent actual raw edges of the original circuit. On a four-set supporting b perfect matchings of R there are binom(b,2) four-cycles; at least b−1 candidate raw pairs are missing if b≥1. As b≤3, each four-set forces at least (2/3) times its four-cycle count in missing pairs. These missing pairs are distinct across four-sets, since a pair of disjoint R edges has a unique vertex union. Hence M≥(2/3)·#C4(R).

## Supersaturation and the exponent

For the g-edge graph R on w vertices let S be the sum of codegrees over unordered distinct pairs. Then S=Σ_v binom(deg(v),2)≥2g²/w−g. Here w=O(E)=O(h^(3/5)), g∼h, so S≫w² and S=Ω(g²/w). Cauchy–Schwarz gives

    #C4(R) = ½ Σ_{i<j} binom(codeg(i,j),2)
           ≥ ¼(S²/binom(w,2)−S) = Ω(g⁴/w⁴).

Using M=O(hE), w=O(E) and g∼h gives hE=Ω(h⁴/E⁴), or E=Ω(h^(3/5))=Ω(n^(3/10)). With uniform constants the additive one in E is immaterial. This proves the regular lower bound.

For an arbitrary sequence of minimum circuits with E≤t^(3/5), follow the three-gate deletion alternative until a regular minimum on m inputs or the four-input base. With r=n−m, s(n)≥r+s(m). The uniform bound s(m)≥−O(1) implies r=O(√n) and m/n→1; the base cannot occur for large n. Since √(2n)−√(2m)≤r, the regular lower bound at m transfers to the original size, preserving the order n^(3/10).
