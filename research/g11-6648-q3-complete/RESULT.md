# L-meta-6648 on the stratum q = 3

Let G be the original eleven-vertex graph from L-meta-6648. Its undirected edges are (0,9), (0,10), (1,4), (1,8), (2,5), (2,10), (3,6), (3,7), (4,8), (4,10), (5,8), (5,9), (6,7), (6,10), (7,9), (8,9). Take an original circuit C with size at most 21, IsLeastAO G C and TopForm G C. Write U for the cardinality of Ustar G C, j for the cardinality of junk G C, c for the cardinality of centreless G C, and q for the cardinality of (orN G C) minus (lam G C). If j≥3 and q=3, then U≤2c+j+3.

**Transfer to the issued conclusion.** For the issued sets X and J, the exact balance is |X|+j=U+|J|. Add |J| to the inequality above, substitute the balance, and cancel j. This gives |X|≤2c+|J|+q. The selected-fiber and disjoint-pair premises are therefore admissible as written; the stronger estimate does not require them.

**Partition.** All gates and counts in the dispatch are those of C. A receiver is a physical OR whose input list contains a wire from an original junk AND. A gate with two such input pins counts once. Let b count these gates, and p count those among them whose output has nonempty orIn raw support. Encountering a mixed signal along an OR path alone does not make a gate a receiver. Each receiver is a distinct member of orN minus lam, so 0≤p≤b≤3. If b=0 every exceptional OR is physically pure by the last-AND-on-a-path argument. The all-pure theorem gives the asserted bound. If b=1 the complete single-receiver theorem gives it. These two alternatives require no further split.

For b≥2 the original size lower bound and the exact card classification give exactly one physical reader of the raw input at vertex 3. It is an OR, a dirty AND, or a clean AND, exclusively. For an OR the sibling is either a dirty AND or a raw-empty OR. The whole sole-OR theorem covers both cases. The whole dirty sole-AND theorem covers both b values. Only the clean AND A remains. For A, split by the original counts b and p as follows.

| b | p | Source establishing U≤2c+j+3 |
|---|---|---|
| 2 | 0 | 6648-q3-clean-b2-p0.md, all signs and ancestries of the third paid OR |
| 2 | 1 | premises_6648_q3_mixed_sign_complete_index.md, both raw-empty and visible S |
| 2 | 2 | premises_6648_q3_two_positive_complete_index.md, including nested, coincident and distinct donor signals |
| 3 | 0 | All-raw-empty theorem and its port-transfer lemma. Here the three receivers exhaust the three paid ORs. |
| 3 | 1 | 6648-clean-b3-p1-complete-index.md |
| 3 | 2 | 6648-clean-b3-p2-index.md |
| 3 | 3 | 6648-q3-clean-b3-p3-index.md |

This enumerates every permitted p in each row. In the b=2 rows the uncounted third exceptional OR can be pure or inherit AND ancestry. The proofs use the original graph edges and Lambda anchors under projection. In particular a visible signal S can survive the 19-to-15 restriction on a relabelled or aliased wire; the physical AND reader that would contradict the 15-gate minimum is tracked separately. No reduced circuit is assumed least unless its own optimum is established.

## Dependency hashes

| Material | SHA-256 |
|---|---|
| Pure / all-empty packet g11-6648-pure-or-empty.tar.gz | 75b48f66c04e6fac566cdab46c829983a7243606aaba9d843e3f65e465efcb6b |
| Single-receiver packet g11-6648-q3-one-entrance-full.tar.gz | 9a4d4047ae2d3874a263ddb00a00f0be40ce897c5585837d3081df24d8629014 |
| Dirty sole-AND packet g11-6648-q3-dirty-sole-and.tar.gz | 09d474023471f9e21007bd92f73813a97b2f089f386e007452538af66abf9ea1 |
| Sole-OR packet g11-6648-q3-sole-or.tar.gz | 123d81d682bd86e0e698dfe3a4d207dbe2fe7f5a031721614a34632ea05e5ee7 |
| Clean b2 p0 | 6a8aa506216a1e8a84203f98f78bc44036adcb598b31b63548a5cc8c76996d93 |
| Clean b2 p1 | 949f870be973b9e8cb35cd8e204a0f50cdfe6f3e7c9e8ada84a044449ee2fd4f |
| Clean b2 p2 | 2b4080774759350f71e7ea353055c40439c2df2dc0682dc67366f2bf82edab30 |
| Clean b3 p1 | 100c886a1344f85011893dca628d87cd8ce2b453890fa42f4c6a15fbfe1a33bf |
| Clean b3 p2 | a6874ab6b88f5cc8f2e1d099aeb0539cc97052f22b985e617fe201f5487fe511 |
| Clean b3 p3 | f0499b88f374768e63893854e5a5fc90dd29f6a0b5e77f1fd520100ccf44db2d |
| Physical classification definitions and refinements | 0889953fa2ad97652a7b0e3ba8756cf3124b54863827faea294404ced3f86a94 |

The earlier cofactor floors, source reductions and finite H8 receipts are identified by the dependencies. This is a mathematical research proof for q=3. An eligible combined Lean proof of the entire official theorem remains outstanding, including the q≥4 cases.
