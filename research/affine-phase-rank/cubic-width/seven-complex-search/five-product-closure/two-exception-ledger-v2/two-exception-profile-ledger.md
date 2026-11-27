# Two exceptional stabilizers among seven rays

Assume five block-product stabilizer rays and two nonproduct stabilizer rays represent the tensor cube of the three-qubit CCZ state g. All three original parties have three qubits. A profile abcz records the Bell multiplicities on BC, CA and AB in that order, followed by the GHZ multiplicity z. Thus each of a,b,c,z is an integer from 0 to 3, the all-zero tuple is omitted, and z+max(a+b,a+c,b+c)≤3. The remaining qubits at each party have fixed local stabilizer factors. The tripartite stabilizer normal form and the three local Schmidt ranks together with the GHZ multiplicity identify precisely these individual profiles. [Bravyi, Fattal and Gottesman](https://arxiv.org/abs/quant-ph/0504208)

There are 38 individual profiles with the parties labeled, distributed as 22, 11, 4 and 1 for z=0,1,2,3. Permuting the parties leaves 15 individual orbits. Repetition is allowed: different rays may have identical normal-form profiles.

| Pair convention | Labeled parties | Simultaneous party permutations |
|---|---:|---:|
| Ordered exceptional rays | 1444 | 347 |
| Unordered exceptional rays | 741 | 187 |

For a Burnside cross-check, a transposition fixes 14 individual profiles and has 12 two-cycles on the others. It fixes 196 ordered pairs and 117 unordered pairs. A three-cycle fixes five profiles, 25 ordered pairs and 15 unordered pairs. Averaging over the identity, three transpositions and two three-cycles gives 347 and 187.

There are 9 labeled biseparable profiles B, one simple-GHZ profile H and 28 other genuinely tripartite profiles T. The six unordered pair categories BB, BH, BT, HH, HT, TT have respectively 45, 9, 252, 1, 28, 406 labeled pairs and 12, 3, 57, 1, 11, 103 simultaneous-permutation orbits. These are raw counts before mathematical exclusions.

**Common cut.** If the two nonproduct rays both factor on the same original cut, their Bell counts concentrate on the same pair of parties. All such pairs are excluded. [Common-cut proof](two-same-cut-exclusion.md)

**Two simple GHZ rays.** The profile pair (0001,0001) is excluded even when the two GHZ encoders differ. [Two-GHZ proof](two-simple-ghz-exclusion.md)

**Other pairs of simple resources.** One single GHZ with one single Bell is excluded for each Bell link. Two single Bells on different links are also excluded. Together with the preceding two tests this covers every pair of simple elementary resources, including independently encoded copies. [GHZ and Bell proof](two-simple-ghz-bell-exclusion.md) · [Different-link Bell proof](two-different-simple-bells.md)

**Schmidt-support test.** At every party, a rank-eight exception requires the other exception to have Schmidt rank at least four. Indeed, on A versus BC write the rank-eight term E as a combination of the other exception F and six product vectors (the target plus five ordinary rays). The BC Schmidt support of E is contained in the sum of F's BC Schmidt support and the span of those six BC factors. If F has rank at most two, that sum has dimension at most eight. Since E has rank eight, equality holds and that sum equals E's BC Schmidt support. In particular it contains g⊗g. But this eight-dimensional support is a proper stabilizer code in the 64-dimensional BC space, and g⊗g has no nonidentity Pauli stabilizer. For the latter fact, a Pauli eigenvector condition on a product splits into both local eigenvector conditions, and the CCZ sign has no nonzero translation derivative that is affine. A nonidentity pure Z Pauli cannot fix the full-support state either. This argument works on each party and with either exception designated E. The local logarithmic ranks equal z+b+c, z+a+c, z+a+b on A,B,C.

| First applicable exclusion | Labeled unordered pairs | Unordered simultaneous-permutation orbits |
|---|---:|---:|
| Common cut | 18 | 6 |
| Two simple GHZ rays | 1 | 1 |
| One simple GHZ and one simple Bell | 3 | 1 |
| Two simple Bells on different links | 3 | 1 |
| Schmidt-support test, additional | 356 | 77 |
| Remaining after these tests | 360 | 101 |
| Total | 741 | 187 |

The [187-row profile ledger](two-exception-profiles.csv) lists the canonical ordered display of each unordered orbit, its multiplicity before party permutations, and the first applicable test. The [enumerator](two-exception-profiles.py) constructs every admissible tuple, every pair with replacement and every simultaneous permutation of the three Bell coordinates. The orbit sizes sum to 741.

An individual profile forgets the local Clifford encoder at each party. Two independently chosen encoders need not be simultaneously reducible to their individual canonical forms, and the target fixes a further reference state at each party. The 101 remaining entries count resource profiles. Determining physical pair orbits and deciding which profiles admit a seven-ray representation require further analysis of the relative encoders. A single-exception bound cannot be imported by deleting the other exception.
