# Large inlets into flattened OR groups

In the no-progress signature model of protected-or-group-403-404.md every OR group has a large top. Shared ORs cannot be small, the output is large, and an OR feeding an AND is either at a nondesignated AND with two large operands or at the large sibling slot of a designated AND whose other operand is its literal raw.

Trace large values backwards within each OR group. Either the group contains a source OR at which two small children produce a large value, or a large inlet is present. At most L groups can have such a source, since each source is a physical OR in a unique group. Here L≤[2(n−p)−u]/(t+1) is the token bound. Every other group consumes a different boundary occurrence. Internal origins are large ANDs or shared ORs. There are A−u large ANDs and at most F shared ORs. Their combined outgoing occurrence count is at most A−u+2F, with F the total internal fanout excess. Protected raws supply at most 2p+E−B occurrences, where E is raw excess and B counts current sole ORs.

Writing G=F+E and using A−u≤L+G+2p−B gives
```
V ≤ L+(A−u)+2F+2p+E−B ≤ 2L+3G+4p−2B.
```
The 5R/6 demand with this upper bound alone suffices at order 405; see check-large-group-boundary.py.

## Joint correction from the incidence group

The incidence lead supplied the following strengthening. A high-degree vertex v (degree at least four) has at most one nonleaf neighbor: if there were two, their necessarily common alternative y joins them, and their edges x₁,x₂ to v are both incident with y. Yet x₁,x₂ themselves must be incident, by shielding at y. This is impossible. Charge an edge e=vw the quantity 1/deg(v)+1/deg(w); their sum counts the nonisolated vertices. An edge neither of whose endpoints is high has charge at least 5/6, since two degree-three endpoints cannot meet. For a high vertex of degree d with zero or one nonleaf neighbors, its d edges have combined charge at least d+1/2: its own contribution is one; at least d−1 other endpoints are leaves; and the last has at most degree two. There are no edges with both endpoints high. Consequently 6V≥5R+Σ_high deg(v).

The L distinct minimal-large source ORs each cost at least t+1 token occurrences in the source's flattened group. Their small expansions cannot branch, so these occurrence charges are disjoint, including when several sources belong to one group. At most u occurrences are designated private tokens. In every low-degree group with a source there are at most three ordinary occurrences. Thus Σ_high deg(v)≥(t−2)L−u. Combining with the boundary upper bound proves
```
5R ≤ (14−t)L+18G+24p−12B+u.
```
For 8≤t≤14 the upper bound on L gives a sufficient surplus condition
```
(7t−23)(n−p) > (7t−8)u+(t+1)(18G+24p−12B).
```
After joint substitution for B its adverse coefficient is 12t−3>0. With H=q−15, the 32-wide adaptive checker reaches order 406 with maximum batch 10 and total cap sum 82038. For order 407 the fixed no-reset envelope first blocks at stage 10176.

## Isolated loops

The review group's L9 observation avoids relying on explicit associative simplification just to exclude equal endpoint tops. When both readers of x reach the same group, any different raw y in that group shields both on its singleton, contradicting the neighbor comparison for x. Thus each loop is the only edge at its vertex and can be removed with that vertex before the graph bound. Restoring this one-edge one-vertex component preserves 6V≥5R+Σ_high deg(v). In the physical group a loop uses two ordinary slots, so it still contributes at most three slots to any low-degree source group.
