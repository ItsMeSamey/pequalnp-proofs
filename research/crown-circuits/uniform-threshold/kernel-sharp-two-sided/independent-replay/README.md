# Independent two-sided kernel replay

The immutable Git commit, tree and manifest digest are in source-lock.json. prepare.sh unpacks that tree. prerequisites.py verifies the 304 source hashes and the axiom-report digest, then builds two Mathlib sources extracted by pinned Git blob into a fresh private overlay. prerequisites.json records those source hashes, resolved input paths and generated object hashes.

replay.py builds all 304 manifest modules consecutively into an empty private output directory. All six PEqualNP sources are included. Each direct application import is checked against the manifest and must resolve under that fresh prefix. Third-party modules come from the pinned packages and private Mathlib overlay. objects.tsv and resolved.tsv retain per-module hashes, completion times and dependency paths.

verify_receipt.py verifies the final evidence including all 304 objects, the two freshly rebuilt third-party objects, the occurrence of the fresh prerequisite in the project import graph, and the public axiom report. statement.txt reproduces the verified theorem declaration, which concerns the minimum circuit size via surplus n.
