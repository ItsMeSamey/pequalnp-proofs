# A quadratic dual certificate on an all-singleton physical theta

Join two poles by three internally vertex-disjoint paths A, B, C, each of length four. Write A1 through A4 and likewise for B and C in path order. Each atom is a distinct geometric request on its own edge. Make three conflict bicliques, using every cross pair of the indicated shores exactly once as a physical two-comparison shell.

| Component | Left | Right |
|---|---|---|
| 1 | A1, A2 | B1, B2 |
| 2 | B3, B4 | C1, C2 |
| 3 | C3, C4 | A3, A4 |

Thus there are twelve distinct shells and 24 indexed comparison occurrences. Every atom appears twice. Internal vertices of the indexed multigraph have degree four and each pole has degree six, so degree-two path suppression leaves only singleton paths. Type sharing recovers the twelve distinct atoms without identifying opposite signs.

Use A+C and B+C as a cycle basis of the geometric theta. Their two equations assign columns a=(1,0) to every A edge, b=(0,1) to every B edge, and c=a+b to every C edge. Given arbitrary edge requests d_e, the failure syndrome target is the XOR of columns on target-one edges. All four targets occur: set d_A1 and d_B1 to the two desired target bits and all other requests to zero. Each biclique has two distinct line spans, which intersect only at zero. With no unlisted atom, the plain common-period and nested-span scan makes no gain.

Fix one allowing shore in each biclique. A dual word (x,y) annihilating every allowed column must annihilate the chosen shore in every component. Without knowing those choices it therefore satisfies xy=0, y(x+y)=0 and x(x+y)=0. On binary words x²=x and y²=y. Adding the first equation to the second yields y=0, and adding the first to the third yields x=0. This is a degree-two Boolean certificate, with no multiplication of the product equations required. Every orientation therefore has trivial annihilator and spans the whole syndrome plane. Their common span is the entire plane. This conclusion concerns the span of each single orientation and hence holds simultaneously for all four syndrome targets.

For an explicit lift choose all left shores, which contain A1 and B3. Fail A1 exactly when the first target bit is one and B3 exactly when the second is one. All other atoms succeed. This has the required syndrome and never fails both comparisons of any shell. Integrate x_u XOR x_v = d_e XOR f_e along a spanning tree, starting at either pole with potential zero. The two cycle equations ensure both remaining edges agree. To realize each shell on fresh raw coordinates (4s+j,4s+j+2), j=0,1, use endpoint offsets 0 and 1 XOR d_e so the raw inequality implements the requested geometric difference. At each geometric vertex pin all endpoint copies to the first with the XOR of their offsets. Setting each raw endpoint to its integrated vertex potential XOR its offset satisfies every pin and every original paired shell.
