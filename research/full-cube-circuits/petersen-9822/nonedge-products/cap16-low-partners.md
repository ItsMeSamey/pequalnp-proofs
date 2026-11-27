# Distinct low inputs cannot share an unsafe monotone OR partner

Use the four sole-reader ORs from cap16-low-transversals.md. Write their sites as g_i=x_i∨P_i. Treat the inverter output as an extra formal input z. Consider any wire W independent of two owners i,j in this formal monotone circuit for which W=1 forces both P_i and P_j true under every setting of z. The same argument applies if W is computed solely from raw inputs and implies both actual partners regardless of the inverter. Assume W is monotone in the raw inputs. Then W implies the full target edge predicate.

Otherwise take an independent witness for W and delete i,j, preserving W. Write B for the resulting independent set. For each owner k in {i,j}, B cannot meet N(k), since adding k would then accept the target while its sole reader stays true. Here both assignments have their actual inversion values: P_k remains true because W remains true. All downstream gates are identical after toggling k because its sole reader is unchanged. Moreover B must dominate every vertex t of N(k): otherwise append t, obtaining an independent set still satisfying W that meets N(k). These arguments require only monotonicity of W, even if the partners themselves use the inverter.

For a single owner, the minimal independent sets avoiding k and N(k) and dominating N(k) are as follows (each row follows by choosing a neighbor other than k for each of the two vertices in N(k)).

| k | minimal sets |
|---|---|
| 0 | {3,7}, {8,9} |
| 1 | {7,8} |
| 2 | {5,6} |
| 3 | {0,6}, {5,9} |

For each distinct pair of rows, two selected sets cannot be contained in an independent set avoiding both owners and both neighbor sets. This checks all six cases and excludes B.

In particular two low entries with identical pre-inversion partner P satisfy P≤F, since its position upstream of both sole entries makes it independent of both owners. More generally for a common partner downstream of the inversion let P0 denote the function with the inversion output cut and set to zero. This is monotone and independent of both owners, and actual P is always at least P0. Therefore P0≤F. Every independent witness for this common partner must have the physical inversion output one, and must cease activating the partner when that signal is clamped to zero. The claim also applies separately to any monotone independent raw-only wire feeding both partners along OR-only paths.

When a physical common partner P itself implies F, replace one of its two injections x_i∨P by raw x_i and append P as a final disjunct. If P is false the rest evaluates identically. If P is true the restored disjunct gives the correct output. P precedes the changed site and is preserved, so this uses the same binary budget even in a signed circuit.

There is a physical AND charge for each low owner with P_i0 positive on some independent input, where the subscript denotes the same zero clamp. Choose such an input and trace a true operand backwards through OR gates from P_i0. This cannot stop at the clamped zero wire. It cannot stop at a raw: an OR-only raw path would force the partner true on that raw singleton and on all its extensions, yet no row in the table has a singleton witness. Thus it reaches a physical AND upstream of the partner with only ORs between it and that partner. Its zero-clamped output is positive on the chosen independent input. Two owners cannot charge the same physical AND by the two-owner impossibility above, applied to that clamped output. Thus k low partners with independent witnesses even after the zero clamp cost at least k distinct physical ANDs, in addition to their distinct entry ORs. Each charged AND is zero on every raw singleton after clamping, by the same single-owner argument. This charge permits further uses of those ANDs elsewhere in the circuit.
