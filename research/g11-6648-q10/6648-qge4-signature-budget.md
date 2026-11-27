# Necessary G11 counterexample signatures with q at least four

Use original, unprojected counts. Write s=16−U for the number of starred graph edges, j for junk ANDs, c for centreless tops, t for ordinary tops, q for ORs outside Lambda below the clean aggregation, and l for the Lambda cardinality. The issued balance makes a counterexample require U≥P+1 where P=j+2c+q. The least size is exactly 21, so normalized clean aggregation gives P+2t+l=22. The established t=0 and s=1 exclusions imply t≥1, s≥2, P≤13. Since j≥3,q≥4, P≥7. The G11 maximum degree four and absence of four-cycles make each ordinary top's raw cross a star of at most four edges, hence s≤4t. At the mask level t≥the vertex-cover number of the starred subgraph (take one center per ordinary top). Neither condition supposes the tops have private raw edges.

## All base cells

Every entry is the inclusive j range at the given q,c; dashes are empty. These 50 triples exactly enumerate the scalar q,c,j bounds.

|q|c=0|c=1|c=2|c=3|total|
|---:|---|---|---|---|---:|
|4|3–9|3–7|3–5|3|16|
|5|3–8|3–6|3–4|—|12|
|6|3–7|3–5|3|—|9|
|7|3–6|3–4|—|—|6|
|8|3–5|3|—|—|4|
|9|3–4|—|—|—|2|
|10|3|—|—|—|1|

For any base row compute P. For each s in the next table take **all** integers t from ceil(s/4) through the stated maximum and set l=22−P−2t. This enumerates every (q,c,j,t,l,s) in the base scalar relaxation exactly once. The size-score bound t+P≤U+6 is automatic here: t≤7 and U≥P+1. Equivalently s≤t+l. Under the same bounds U ranges from P+1 to 14.

|P|base multiplicity|s|t maximum|2t+l|number of (s,t,l) choices|
|---:|---:|---|---:|---:|---:|
|7|1|2–8|7|15|45|
|8|2|2–7|7|14|39|
|9|4|2–6|6|13|28|
|10|6|2–5|6|12|23|
|11|9|2–4|5|11|15|
|12|12|2–3|5|10|10|
|13|16|2|4|9|4|

There are 692 six-tuples before any additional graph-mask, cofactor, reader or supplier tests. The column of (s,t,l) possibilities equals (14−P) floor((22−P)/2) minus the number of integers s≥5 in 2,…,15−P. The 692 entries enumerate a relaxation only; no realizability conclusion follows. These are algebraic counts, with no new numerical run.

## Existing graph-mask filter, separately

Given an independent ambient vertex cover A of the actual nonempty starred edge mask, write R=V(stars) minus A, and f(A) for a proved floor on the true-A cofactor. The independent-cover argument gives P≥f(A)−|R|+1, with a stronger bound when a counted paid OR is reached from A. The existing basic sweep uses the maximum of this lower bound over available A; absence of an independent cover gives no exclusion. The prior receipt lists the following mask exclusion counts in the q≥4 range. Entries run in ascending P order; smaller filters with the same P,s need not hit a specific actual mask.

|s|number of masks|P values|excluded mask counts|
|---:|---:|---|---|
|2|120|7–13|111,79,66,32,17,10,3|
|3|560|7–12|155,83,31,6,2,0|
|4|1820|7–11|60,18,1,0,0|
|5|4368|7–10|5,0,0,0|
|6–8|varies|admissible P≥7|0 throughout|

No entire (P,s) column above disappears from the basic independent-cover sweep. The pre-existing floor inventory used 124 cases; the combined contraction and table do not have a Lean receipt in this audit. See quantifiers_6648_star_receipt.txt, quantifiers_6648_star_summary.json and 6648-independent-star-cover-restriction.md. The graph lower bounds, topology-specific results and stronger cofactor cuts must not be represented as the same evidence as the scalar enumeration. In particular the all-physically-pure and all-raw-empty cases are already proved globally but are not detectable from q,c,j,t,l,s alone.
