# Repeated endpoints in incidence parses

Let F accept when some active point and active line are incident in a projective plane of order q. An accepting parse chooses one true input to each OR and both inputs to each AND. Leaf multiplicities count occurrences in the unfolded parse, including repeated uses of a shared wire.

## Sparse inputs

Choose q+1 distinct marker lines. For each marker b, form a factor H_b from the disjunction of variable b and the incidence predicate with b deleted. Thus H_b equals F OR b. The conjunction of these factors equals F whenever at most q lines are active, since simultaneous activation of every marker requires q+1 lines. Every factor is indispensable on sparse inputs. Activating the other q markers and no points makes only H_b false.

Take a singleton flag whose line is outside the markers. Each factor accepts this flag, while either endpoint alone makes the factor false. Every accepting parse of the factor must therefore use both endpoints, since setting an unused leaf variable to zero preserves the parse. The conjunction requires at least q+1 copies of each endpoint.

## All inputs

Fix 1 ≤ k ≤ q. Choose k distinct points on a common line and pair each with another line through it. Each paired line meets the common line only at its partner, so the selected vertices induce a matching of size k.

For each set C choosing one endpoint per matching edge, build a factor H_C that accepts if a vertex of C is active or an incidence edge disjoint from C has both endpoints active. Every active incidence edge makes every factor true. On an independent input, choosing an inactive endpoint per matching edge gives a C for which H_C is false. Thus the conjunction of the 2ᵏ factors equals F everywhere.

Each factor is indispensable on sparse inputs. Activate precisely the matching endpoints opposite C. These form an independent set and include at most k lines. Every other choice D contains an active endpoint, while H_C is false.

Take an unchosen point of the common line and the common line itself. This flag avoids all matching vertices. At the singleton flag, each factor requires both endpoints in every accepting parse, since it rejects each endpoint alone. The output requires at least 2ᵏ copies of each endpoint.

Both circuits admit binary gates by implementing the restricted predicates as disjunctions of edge conjunctions. These examples concern arbitrary circuits with indispensable output factors. They leave the minimum-size circuit case open.
