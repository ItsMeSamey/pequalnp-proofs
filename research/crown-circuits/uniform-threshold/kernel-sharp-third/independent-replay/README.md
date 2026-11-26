# Independent sharp lower kernel replay

The source archive was extracted from the Git commit and tree in source-lock.json. All 268 Lean sources and both the manifest and axiom report were verified before the single-compiler build. The terminal theorem statement is preserved in statement.txt.

prepare.sh extracts a fresh source tree. replay.py builds all manifest rows, including six PEqualNP definitions. The first import path is a new empty output directory. All remaining paths are pinned third-party caches or the standard library. Every local dependency is resolved and logged before compiling its consumer.

After completion verify_receipt.py rechecks the 268 rebuilt object hashes, sources, local import edges, external dependency paths, and the final axiom report. objects.tsv and resolved.tsv are the per-module object and import ledgers. The generated object tree is intentionally held until receipt publication.
