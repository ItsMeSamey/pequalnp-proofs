# The four-input cut for the seven-AND quartet architectures

Let p be 5 or 6. The pure prefix supplies p vertex banks, each the OR of its incident raw bits. The pure–pure raw inputs form a clique on p−2 vertices, plus two isolated vertices. Every other raw input has one occurrence in a pure bank and one designated occurrence as an operand of a mixed OR. The other operand of each designated OR is a nonraw antecedent. There are at most p−3 additional tail ORs. Only the entire pure-bank outputs and the designated mixed raw occurrences enter the tail. Every pure bank has a path to the output in the original trimmed physical circuit. A distinguished bank Q has four distinct incident raw labels. The other degrees are one two and the remainder three.

Under these hypotheses the circuit cannot compute threshold two. The proof does not require a particular ordering of the tail gates, the bound on Q readers, or the mixed-component separation condition.

**Contraction.** First hold all pure roots formal and set designated raw occurrences outside Q to zero. Their OR gates become identities on their nonraw operands. Contract only these identities. Every original path from a pure-bank output to the final output persists: such a path uses the nonraw operand of every bypassed gate it meets. No pure root is downstream of another in this interface.

**Zero restriction.** If a signal with a path to the output is set to zero and the restricted function remains nonconstant, at least one further OR can be removed. Follow the path. Any AND receiving the propagated zero is zero. An all-AND path to the output would make the restricted function constant. Therefore a first OR is reached and can be bypassed to its other operand. The same argument works when several signals are jointly set to zero if at least one of them has an output path. Two assignments giving different outputs while differing only on these signals certify such a path even after earlier circuit simplifications.

At every stage we retain the assignments supported on Q's four raws, so the restriction remains nonconstant. On these assignments Q is one whenever at least one raw is selected. At the end it can be fixed to one: agreement with threshold two on the four singleton inputs and all six pairs suffices on the whole cube by monotonicity. Threshold two on four variables requires four ORs. The accompanying four-or.cpp verifies the lower bound by exhausting three ORs with free unlimited ANDs on these ten boundary inputs.

## Q in the clique

Q has p−3 pure–pure incident edges, hence 7−p private raws with designated mixed ORs. The first contractions leave at most (7−p)+(p−3)=4 OR gates. A pure isolate D has no raw shared with Q, so its bank may be set to zero on the quartet restriction. Its original path survived contraction, hence this step eliminates at least one further OR. Set all other bank inputs to their true values on nonempty assignments supported on Q. Each other clique bank is the raw of its unique edge to Q and each remaining isolate is zero. Fix Q to one. The resulting four-input threshold circuit has at most three ORs, a contradiction.

## Q isolated

All four Q raws have designated mixed ORs. The initial contractions leave at most p+1 ORs. Keep Q formal during the following clique witnesses. The other isolated pure bank E has a surviving path, so setting E to zero removes at least one OR. This is compatible with any raw assignment supported on the Q star and pure–pure clique edges.

Delete p−4 clique-bank inputs one at a time. Before each deletion, at least three clique vertices remain. For the vertex v to be deleted, select two distinct other remaining vertices u,w. The singleton raw edge uw and the pair of raw edges uw,vw give different outputs while differing only at the formal bank v. In particular no mixed raw is injected on either input. Thus v is essential even after the previous deletions, and setting it to zero eliminates at least one OR.

Let u,v denote the final two clique banks, and q any Q-private raw. The singleton q and the pair q,uv give different outputs and differ only at banks u and v. The pure–pure raw uv has no mixed occurrence. Setting both banks to zero thus removes at least one further OR. The total number of extra OR losses is at least 1+(p−4)+1=p−2; only three of the original p+1 ORs remain. Fix Q to one on nonempty quartet inputs to reach the same contradiction.
