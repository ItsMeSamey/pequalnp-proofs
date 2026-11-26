# One shared OR aggregate in the bank preprocessing

**Theorem.** The sharp 41-gate bound survives when the OR banks may reuse one common aggregate of arbitrarily many paired inputs. Its fanout into distinct banks is unrestricted. Within the OR preprocessing there is at most one reusable aggregate, in addition to the raw paired inputs. The tail is an arbitrary binary monotone formula on bank outputs.

Write w for the OR of k distinct paired inputs, and let C be the c distinct bank outputs whose computations reuse w. The case k<2 or c<2 is already covered by the independent-bank theorem. Duplicate direct inputs in a bank and duplicate paths from w to a single bank can be removed. Expanding w separately into each of the c bank trees costs at most (k−1)(c−1) extra gates. This includes the case that w itself is a bank output. Unused banks can first be dropped.

Normalize singleton label supports as in the independent-bank proof. Let (N,B) be (12,5) in the ordinary case or (11,6) after setting aside a one-occurrence singleton label occupying at least half the space. That singleton cannot be one of the k grouped inputs, since c≥2. Every group support contains C. The antichain property requires at least one additional bank per group label: a support equal to C would be contained in every other group support. Let a count all group memberships beyond these c+1 per label. Let b count all memberships beyond two per outside label among the N labels. The total excess over two memberships among the N labels is k(c−1)+a+b. Using the possible sharing savings in the circuit gate count therefore gives

    E ≤ B − (c−1) − a − b,

where E is the sum over represented banks of formula occurrences beyond their first occurrence.

For the group tests fix the c common bank outputs to one, fix irrelevant banks to zero and simplify the constants in the formula. This preserves the group diagonal tests and distinct group-label unions. At least k−a of the residual supports have just one bank. They are distinct and private within the restricted group, by the antichain property. Their restricted zero-certificate masses are at least 2 raised to minus their original bank occurrence counts, since restriction cannot increase occurrences. Their sum is at most one and is strictly below one if there are further group labels. When k≥3, at most one residual singleton can have occurrence count one. Thus k−a−1 ≤ E and k ≤ B−c+2. The case k=2 is included directly.

There are at least N−k−b ordinary pair labels outside the group. For these use the refined pair-slot bounds of the arbitrary-formula proof. Charge exactly the chosen clean heavy pairs at the ordinary rate and the remaining heavy-pair slots at the doubled rate. Also double the second heavy–light slot at each touched heavy. Enumerating nondecreasing heavy profiles with the above E cap, and testing the restricted singleton sum against the most favorable available bank weights, leaves five cases. The group labels have additional positive measure, so first-pass pair bounds at or above the available whole-space measure already suffice.

In every remaining case c=2 and a=b=0. The group labels have support C plus one private bank apiece. Assign the available heavy banks to the two common positions and the k private positions in all possible ways. A pair of common banks, or a pair comprising a common and a group-private bank, cannot be an outside pair label because its support is contained in a group support. Remove these forbidden heavy-pair slots. If w_C is the sum of the two common occurrence counts and tᵢ the private occurrence counts, the global group-label events contribute at least 2 to the power −w_C times the sum of 2 to the power −tᵢ. The latter sum must also be at most one on the restricted group tests.

| Labels N | Group k | Heavy weights | Least combined measure | Available |
|---:|---:|---|---:|---:|
| 12 | 3 | 2, 2, 2, 2 | 17/16 | 1 |
| 12 | 3 | 2, 2, 3 | 33/32 | 1 |
| 12 | 4 | 2, 2, 2, 2 | 1 | 1 |
| 11 | 4 | 2, 2, 2, 3 | 5/8 | 1/2 |
| 11 | 4 | 2, 3, 3 | 21/32 | 1/2 |

Equality in the third row requires both common banks to be light, all four private group banks to have weight two, and exactly four selected clean heavy–heavy pair labels. Each group label's zero-certificate event must then attain its bound of 1/16. Its deepest-AND core is nonempty, since a conflict doubles the bound. Its four occurrence demands must lie on four distinct axes, since otherwise its core would occupy at least 1/8. The two common axes therefore do not occur in any of the four private cores. The four group cores are disjoint. If two private cores were compatible, their intersection would still be compatible with the fixed common choices, contradicting disjointness of the corresponding group cores. Hence all private cores are mutually disjoint. These private banks are all four heavy banks, so no heavy–heavy pair can be clean. This contradicts the required four.

The matching 41-gate construction uses independent grid banks. The verifier single_shared_bank_volume.py uses the profile helper from endpoint_volume.py. Allowing two or more shared aggregates in the bank preprocessing or allowing shared internal tail gates falls outside this result.
