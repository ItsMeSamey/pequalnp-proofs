# Width inventory after the hidden-successor test

Four distinct nonempty pairwise-linear raw operands have exact OR price p equal to the sum of their widths minus four. A product of two distinct singleton scopes is either an edge monomial, which is safe, or a nonedge monomial, which is unproductive. Thus at most two of the four scopes are singletons, and any two singletons must belong to different products. An operand contained in its partner permits an immediate AND bypass. For any named gate the exact remaining local test is that its trace meets both the thirteen edge inputs and the sixteen maximal independent negatives. The following sorted width lists are necessary possibilities, without assigning the four scopes to H,Q or asserting that any actual prefix completes.

| p | Width tuples (digits in ascending order) |
|---|---|
| 0,1 | none |
| 2 | 1122 |
| 3 | 1123, 1222 |
| 4 | 1124, 1133, 1223, 2222 |
| 5 | 1125, 1134, 1224, 1233, 2223 |
| 6 | 1126, 1135, 1144, 1225, 1234, 1333, 2224, 2233 |
| 7 | 1127, 1136, 1145, 1226, 1235, 1244, 1334, 2225, 2234, 2333 |

For p≥8 the uniform proof h5-raw-prefix-hidden-escape.md excludes all normalized three-sink 0+3 layouts, including non-linear raw scopes when p is computed by exact shared OR pricing. The previously tested 4332 and 3333 families remain independent controls. The singleton terminal case U=H is separately excluded at all prices: H is a nonsink, so some later hidden product has an operand containing H. Redirect that product to its other operand. On H=1 the change has no effect; on H=0 the final output stays zero. This saves an AND without increasing OR count. The five-AND impossibility applies.

At p=7 at most two residual OR gates are outside the four raw prefix cones. U needs a join and some OR outside its cone must carry a hidden label from U to a leaky sink. All signals inside the U cone vanish on every such sink's leakage row. Hence U has exactly one join and there is just one escaping gate. If U=H∨Q, both hidden sources require the same escaping gate E. It must contain both H and Q, hence U implies E. Replacing any sink with E as an operand by its other operand preserves the terminal result, saving an AND. The remaining U is H∨Y with Y raw. It has only two clauses, hence rejects at most two maximal negatives. No p=7 triple leak survives. For the outstanding pairs, the two corresponding covers share five vertices. Since A and B in H share at most one, Y must contain at least four labels. In a minimum linear prefix library it is inside one target. This excludes width tuple 2333 for these pairs. The other p=7 tuples above require further testing; no qualification at lower price is inferred.
