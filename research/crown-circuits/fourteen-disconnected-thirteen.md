# Disconnected thirteen-flag hosts at fourteen inputs and eight ANDs

Use a regular size-34 eight-AND host computing threshold two on fourteen independent edge labels. The simple incidence graph has q=13 nonisolated flags and its decoder has eleven ORs. The known degree cap is four and a branching pure flag exists. A branching pure flag of degree two or three has two direct OR readers; every adjacent leaf flag pays its distinct mixed injector on simultaneous erasure. These local statements do not need connectivity.

The fixed-bank component charge retains a base with at least two edge labels and no flag true on every singleton. Each remote connected component on s flags peels to an anchor edge at cost s−2 ORs. Identifying the anchor endpoints as one independent raw increases the minimum by two more ORs. Thus each remote contributes its full order to the lower bound on the original decoder. Within a connected component, vertices outside a retained connected edge subgraph can be peeled at one OR apiece in decreasing distance. Extra edge labels can be discarded. All costs count decoder ORs.

## Branch of degree two or three

Erase a branching pure flag of degree d≤3 and its t adjacent leaves. The residual has N=12−t nonisolated flags, 14−d edges, and at most 9−t=N−3 ORs. A residual component or union on h flags with local floor h−2 and no universal singleton flag is fatal by the remote charge.

Any component on h≥6 flags qualifies. It has at least five edges and maximum degree four, so no universal flag. A cubic or quartic gives the connected star floor h+dmax−5≥h−2; paths and cycles on at least six flags have floor h−2. On at most five flags any connected cyclic graph other than a cycle has a vertex of degree at least three and has no universal flag. It again qualifies. A five-cycle needs three ORs. Therefore every cyclic component is a triangle or square; any two jointly qualify by the existing floors of four ORs for two triangles, five for triangle plus square, and six for two squares. There is at most one such component. All remaining components are trees of order at most five. By vertices minus edges their count is N−(14−d)=d−t−2. If this is negative the graph is impossible; otherwise

    12−t = N ≤ 4 + 5(d−t−2) ≤ 9−5t,

also impossible.

## Branch of degree four

If the component H of the quartic is not the bare star, it has more than four edges and no flag covers every edge. Its connected degree-four star bound is h−1. The remotes charge their full orders, so the decoder needs q−1 ORs.

**Star and cycle.** A four-edge star together with a disjoint cycle on l≥3 flags requires at least l+4 decoder ORs, with unrestricted AND count. On the star alone its center is the nonemptiness signal of the four independent leaves. Set the center true: every nonempty input is unchanged and empty still rejects by monotonicity below a negative singleton. Thus the star alone needs four ORs by the ordinary floor.

Suppose the combined decoder used at most l+3 ORs. Every cycle flag z spoils some star edge, meaning that formally adding z alone turns its negative singleton positive. Otherwise peel the l−3 vertices outside z and its two neighbors, then pin z true. The neighbors become two independent virtual raws on the incident edges. With no virtual raw the star singletons still reject by harmlessness; each virtual singleton is a negative cycle edge; each pair contains two distinct edges and accepts. Only six ORs remain. But adding one independent raw to the four-star bank costs at least one OR: the raw is essential and a positive survives at zero, so a first OR vanishes on its erasure. The enlarged bank has no flag true on every singleton, so the second independent raw costs at least two further ORs by the fixed-bank independent-raw increment. This requires seven.

Every spoiler witness uses only the individual cycle vertex and one star edge, hence survives prior erasures on the cycle. A positive star pair survives each erasure, so every cycle vertex costs an OR. After all l are erased at most three ORs remain, impossible for the star. This proves the asserted local floor.

The complement of the bare star has eight flags and ten edges, so contains a cycle. Keep a simple cycle in one component and peel the other vertices there. Charge any additional components at full order, as the retained star-plus-cycle bank has no universal flag. The resulting decoder OR lower bound is q−1, exceeding q−2. At arbitrary q, this also excludes every four-star component with a cyclic remote; in particular it excludes the bare star at q≤15 where the remote ten edges lie on at most ten flags.

## Dependencies

Physical roles and simultaneous peeling: degree/t14-34/eight-and-overlapping-branches.md, degree/t14-34/eleven-branch-roles.md, geometry/fourteen34/eight-and-high-degree.md and geometry/fourteen34/connected-twelve-separators.md. Local floors and independent-raw transfer: geometry/fourteen34/connected-large-balanced.md, geometry/fourteen34/two-squares-connected-thirteen.md, comb/fourteen-construct/twelve-component-final.md, comb/fourteen-construct/independent-raw-or-increment.md, comb/fourteen-construct/triangle-and-square.md and comb/fourteen-construct/two-triangles-four-ors.md. The deduction uses no host census.
