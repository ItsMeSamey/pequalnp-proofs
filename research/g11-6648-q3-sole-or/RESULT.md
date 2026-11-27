# Sole OR reader at vertex 3 for q=3

For the original least size-21 TopForm G11 circuit with j≥3 dirty ANDs and q=3 paid ORs, assume vertex 3 has a unique raw reader and that reader is an OR. The original residual-edge number satisfies U≤2c+j+3. This is a source synthesis of branch proofs. There is no combined Lean proof.

Count physical OR gates directly reading at least one dirty AND as b. The sibling of the sole raw input is a dirty AND (Oa) or raw-empty OR (Oo), by the sole-port shielding and top-form reduction. Tracing the dirty input back forces b≥1; every direct entrance is paid, so b≤3. For Oo the reader M is already a separate positive nondirect paid gate, making b=3 impossible.

| Branch | Frozen proof |
|---|---|
| b=1, either sibling | [Signed single-entrance result](sources/site-team-03/freeze-6648-q3-one-entrance/RESULT.md), included in full in prior/g11-6648-q3-one-entrance-full.tar.gz. Historical research commit prefix 67748fab. |
| b=2, Oo | [Oo placement index](sources/site-team-03/freeze-6648-oo-b2/INDEX.md), including the team 08 serial lemma. |
| b=2, Oa, Q outside D's strict cone | [Nonupstream proof](sources/site-team-03/twin_6648_oa_b2_nonupstream.md), for either sign, including bypasses. |
| b=2, Oa, Q strictly upstream of D | [Empty Q](sources/site-team-03/6648-oa-b2-upstream-empty.md) and [positive Q](sources/site-team-08/6648/upstream-positive-q3-fcfe20b9.md). |
| b=3, Oa | [Dispatch by zero, one or two upstream gates and signs](sources/site-team-03/singleton_6648_q3_three_direct_dispatch.md). |

The seven-row finite core replay, the dedicated seven-edge ledger, and the positive controls are identified by full hashes in the [single-entrance result](sources/site-team-03/freeze-6648-q3-one-entrance/RESULT.md). The byte copies are in the full signed prior packet. Earlier q1, q2, c0q2 and pure-or-empty proof packets are included for their prerequisites; they do not enlarge the conclusion. Historical status tables in the dependency sources record their own dates and are superseded for this row by the branch dispatch above. PAYLOAD.sha256 binds every file except itself.
