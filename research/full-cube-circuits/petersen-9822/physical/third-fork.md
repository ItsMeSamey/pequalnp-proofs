# Three distinct shared gates at fifteen signed binary gates

The signed private-chain lemma gives unique readers of raws 1,2 in the form x_i OR P_i up to output sign, with distinct shared earlier binary signals P_1,P_2. The other-raw background zero gives x_1 AND x_2. Turning on exactly 6 and 7 among the other raws gives x_1 OR x_2.

Follow each raw up to its first gate of fanout at least two, or the output. The segment before that point is unique. Its side inputs are independent of the raw, and the signed value at the endpoint is unate with a fixed direction in that raw. Every influence of the raw passes through this endpoint.

Raw i cannot reach P_i as first fork because P_i precedes its only reader. It also cannot reach P_j first for j the other owner. P_j is independent of x_j. On both displayed backgrounds it must vary with x_i because x_i is essential and every path passes through P_j. On the AND background, x_j is pivotal at x_i=1 so P_j(1)=0, forcing the signed guard to equal NOT x_i. On the OR background, x_j is pivotal at x_i=0 so P_j(0)=0, forcing it to equal x_i. That contradicts fixed unateness.

At least one of the two raws reaches a fork before the output. Otherwise their paths merge at a binary gate; on both backgrounds all path segments from the raws to the merge and from the merge to the output must transmit their operand since both raws are essential. The outside side signals are independent of the raws, and the signs along every transmitted edge are fixed. The same signed binary truth table would therefore result on both backgrounds, contrary to the two different sections.

This yields a third shared binary gate distinct from P_1 and P_2. The fanout excess is six at fifteen gates on ten essential raws, leaving at most three units on raw inputs. The proof uses the physical DAG before restriction; it does not require raw fanout to survive pinning.
