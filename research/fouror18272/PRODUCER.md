# Conditional four-OR receipt verifier for L-meta-18272

The producer covered all 55 first-OR shards and recorded 85,164,145 fourth states with zero hit records. Independent semantic replay by team 07 is pending. The two interim manifests permit comparison against prior receipt audits for first indices 1–31. The authority for complete producer counts is the original receipt streams and the recomputed producer index. The final checked status remains pending.

## Check the snapshot

From the extracted directory run:

```sh
sha256sum --check --quiet SHA256SUMS
python3 -B verify.py receipts --use-legacy-zero --split32 --status \
  --review-manifest independent/orcut18272-first1-15-audit-manifest.json \
  --review-manifest independent/orcut18272-first16-32-partial-audit-manifest.json
```

Python 3.8 or later and GNU sha256sum suffice. Status mode exits successfully when supplied evidence passes its checks. Without that flag the verifier exits 3 while any required evidence is missing. A malformed receipt or a hit fails verification.

## Freeze a later complete result

The issued statement, eleven raw masks and frozen C99 source are included. To reproduce a single shard on scheduled compute, compile `source/orcut18272_four_coarse.c` in C99 mode with a compiler supporting the GNU trailing-zero builtin, then pass `FIRST 0 10000`. Gzip the complete output as `fast-FIRST-0-10000.log.gz`. Assemble final receipts in a separate directory. The verifier checks consecutive first, second and third indices, closure records, per-shard counts against the established three-OR reference, and zero hit records. It rejects incomplete streams and extra records after closure.

Shard 0 uses historical C++ records for second indices 0–25 and a C99 stream for 26 onward. Its text digest binds the ordered list of five filenames and SHA-256 values in the verifier. To use a fresh complete C99 shard 0, omit `--use-legacy-zero`. A duplicate shard 0 is rejected. Shard 32 keeps all three gzip files from its interruption and restart. The verifier checks continuity at second 35, third 103, the second-35 resume closure at 121, then the fresh second-36 tail. The shard-32 text digest binds the ordered filenames and their exact compressed bytes.

## Independent replay before checked release

`producer-index.json` records each original first index and its 40-bit output mask, canonical second/third/fourth counts, zero hit records and receipt binding. `producer-status.json` contains the complete producer summary and the digest of the normalized index fields.

The `--review-manifest` option checks historical producer-receipt reviews. Each uses a `receipts` or `completed` array. These reviews and a producer-only count cannot authorize a checked result. The final reviewer is the independent team `/root/site_team_07`. Their semantic replay must cover every shard. They must supply a normalization evidence file documenting their implementation, raw counts and how independent paths map to the canonical producer shards. Different chronological orderings need not give equal raw counts. A per-shard signed adjustment must be justified from this separately reviewed mapping; an adjustment obtained merely by subtracting two totals does not establish correspondence.

Obtain the final confirmation file and its SHA-256 from team 07 via a trusted channel. It must have the following fields:

| Field | Required value |
|---|---|
| family | L-meta-18272/exactly-four-productive-OR/at-most-seven-taps |
| reviewer | /root/site_team_07 |
| statement_sha256 | SHA-256 of instance/statement.lean |
| source_sha256 | SHA-256 of source/orcut18272_four_coarse.c |
| canonical_receipt_set_sha256 | Digest reported for the final producer receipts |
| normalization_evidence_sha256 | SHA-256 of the independent normalization evidence file |
| scope | independent semantic replay and adjusted canonical count correspondence |
| shards | 55 entries, one for each first index |

Every shard entry must give `first`, `first_mask`, `reviewed: true`, `hits: 0`, `receipt_sha256_text`, `raw_fourths` and `signed_adjustment`. The verifier checks that raw fourths plus the signed adjustment equal the corresponding producer count for every shard. When implementations use the same normalization, the documented adjustment can be zero. Report any incompatible normalization to the reviewer; do not manufacture an offset.

For checked verification, omit `--status` and add `--confirmation FILE --confirmation-sha256 HASH --normalization EVIDENCE`. Only a matched 55-shard semantic review gives exit 0 in this mode. The external hash pin binds an authenticated review to specific bytes; it cannot authenticate its own source. This producer-only archive contains neither a completed independent four-OR replay nor a final confirmation.

## Mathematical scope

The earlier archive at `reference/three-or-bound.tar.gz` contains the reduction and both complete enumerations for up to three productive ORs with eight taps. A productive OR enlarges the intersection closure. The extension grants unrestricted intersections between productive ORs. At the fourth OR, it keeps old multirow clean terminals and intersects the new output with each earlier mixed operand. Intersecting a previously clean terminal only shrinks it; high-only masks cannot contribute positives. A meet involving two distinct raw inputs supplies at most a positive singleton, and every low singleton is already available.

For sixteen positives, a cover by at most seven terminals is possible exactly when a subset of multirow terminals covers at least nine more rows than its number of terms. Any remaining rows can use singleton terminals. The C99 source checks this condition under canonical OR ordering. A complete zero-hit enumeration, with the earlier archive, would imply at least five productive ORs whenever at most seven terminal pairs are available. At eight intermediates and seven taps, at least three ANDs are required, leaving exactly five physical ORs in any remaining witness. The remaining five-OR case is open. The analysis is computational and supplies no Lean kernel proof.
