# Thirteen-input threshold and crown

A binary monotone circuit with free fanout needs exactly 32 gates to compute threshold two on thirteen inputs. For inequality on one-hot left and right inputs, the exact size is 45. The global assembly appears in thirteen-exact-assembly/RESULT.md. Keep the directory layout when replaying the component checks.

For the four-group case use verification/thirteen-four/final-crosswalk.md in place of the longer historical host route mentioned in RESULT.md. The short crosswalk covers all 351 starting rows, before any host wiring is chosen. Its four classes have 195, 80, 14 and 62 rows. The last class uses 25 distinct CNFs, provided together with their DRAT proofs. Run the following quick checks from this directory.

    python3 -B thirteen-low-31-cert/check32.py
    python3 -B verification/thirteen-four/final_crosswalk.py
    python3 -B verification/thirteen-four/two_clean_verify.py --mapping-only
    sha256sum -c SHA256SUMS

For full two-clean verification compile tools/drat-trim.c, install the Python dependencies in degree-reproduction.txt, and set DRAT_TRIM to the absolute path of the compiled checker when running two_clean_verify.py with no arguments. The six-group and three-group proof drivers regenerate their proofs and validate them with drat-trim. Their immutable ledgers record CNF digests. degree-reproduction.txt gives the individual commands. Its original absolute drat-trim.c location corresponds to the included tools/drat-trim.c.

The two earlier finite packets thirteen-seven-five-pure-two-cert and thirteen-seven-six-pure-three-cert each contain their frozen model tables, SHA256SUMS and replay instructions. The five-group proof with three branches uses the four-port addendum for four clean terminals and five-three-three-terminals.md for three clean terminals. The ten-input minor requires the restricted no-quartet lemma in degree/t13-seven/ten-no-quartet.md.

## Independent checks

The whole-assembly reviewer examined the frozen RESULT.md with SHA-256 9a9430cc11edb46be59a0941ba981078dec679a1b761236f6425a4a902b313d1, audited coverage across AND counts, pure-group and branching cases, checked applicability of the ten-input minor and reproduced the upper circuit on 8192 assignments. This review relied on the finite endpoint certificates. For the five-group two-branch packet the independent check covered the source, crosswalk, hashes and recorded counts. The 22 full search jobs were performed by the producer. Two separate proof readers reviewed the four-group exit count. The three-terminal five-group proof received an additional independent source review at SHA-256 2eac8aa84b9231d1b9825bb4834920167e68240916ebc1169cc2d4a1af4d4393. The four-group checks are detailed in verification/thirteen-four/p4-audit-receipts.md. This is a mathematical and computational proof assembly. End-to-end Lean verification is open.
