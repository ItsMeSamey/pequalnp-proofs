# Circuit fork certificates

Verify lower bounds for single-output Boolean circuits from a partial truth table, an input-polarity model and finite witnesses. Binary AND, binary OR and unary NOT each cost one gate. Fanout is free. An application may add a fixed cost for physical gates outside the tail.

Run `python -BO check.py` with Python 3.10 or later. Use `python -BO check.py --application xor2` for the smallest example, `--tests-only` for constructive soundness tests, or select canonical21, four19 or four20 for a source-bound application. Dependencies are included or in the standard library.

| Application | Input interface | Patterns | Fixed gates | Tail lower bound | Total lower bound |
| --- | --- | ---: | ---: | ---: | ---: |
| xor2 | Two positive bits | 4 | 0 | 4 | 4, attained |
| canonical21 | Six-gate prefix and 21 positive features | 469 | 143 | 28 | 171 |
| four19 | Four-gate prefix, 22 features and an optional complement | 498 | 141 | 30 | 171 |
| four20 | Four-gate prefix, 22 features and an optional complement | 496 | 141 | 30 | 171 |

The graph examples concern the specified scalar replacements of L-meta-20579 shard 53. Each restricted implementation exceeds the target by at least one gate. The unrestricted instance and its payout remain open in these examples.

## Manifests

The independent engine files live in engine/. Each applications/*/application.json names its source reconstruction, pins external input files and normalized care labels by SHA-256, describes the scope and budget, and identifies the certificates. Pattern integers use slot zero as their least significant bit. The normalized care digest hashes compact JSON serialization of the sorted [pattern,label] pairs.

The free-complement applications bind every 23-wire receipt to all 711 constrained physical rows, then use 22 logical coordinates and explicit liveness cases. The driver checks the positive-only and negative-only branches, the branch with both physical wires live, and a pivotal pair excluding omission of both. The both-live case explicitly excludes four unrestricted first-branch groups. These distinctions matter because a wire merely offered as an input need not appear in a pruned circuit.

## Soundness checks

The tests enumerate concrete gate DAGs and compare the computed fork classes, orientations and permitted orders with the verifier. They cover complete and partial tables, nested branches, complementary source wires, corrupted certificates and false lower bounds on realizable circuits. A separate ordered-region test constructs satisfying assignments for clauses derived from small monotone DAGs. The canonical application also rebuilds and verifies a RUP proof concerning the operand of a sole inversion.
