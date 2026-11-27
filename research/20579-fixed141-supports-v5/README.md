# Frozen 20579 shard 53 fixed-interface ledger, v5

The fixed interface comes from the pinned 183-gate source at output wire 246. At depth five, remove wires 116 and 190 and add 122. The 31 resulting wires are listed in the interface receipt. Retain all 141 upstream gates, including the marker at wire 69, NOT of wire 68. A decoder pays for every new AND, OR and NOT. It may optionally read the already-paid marker. All claims concern this physical price and the 1,024 cells of the posted graph.

Of 583 separating supports that omit the marker, 570 have certified lower bound at least 171 and 13 have lower bound 170. All 583 separating supports that read the marker have certified lower bound at least 171. These results leave 13 of 1,166 supports unresolved at cap 170. A global circuit lower bound or a result with unused-prefix refunds would need additional evidence.

## Verify the ledger and its provenance

Keep the ZIP and use its published SHA-256 to authenticate it. Extract the archive and run:

    python -B review_frozen_v5.py /path/to/fixed141-v5-portable.zip

This checks every inventory member, all artifact hashes referenced by v4, v5 and the interface audit, graph identity, marker structure, support IDs, independent result receipts and the final join. It uses only Python's standard library.

## Fresh numerical replay

For support 12, the frozen historical original implementations, generator, inputs, final schedule and receipts accompany a relocation wrapper. From the extracted directory run:

    python -B relocate_support12.py . --verify

This is a new numerical run. The wrapper was source- and hash-checked during packaging. The packager did not execute this numerical command. The first 960 of the historical 4,642 schedules were processed by two implementations in the same pilot process using the alternate /tmp lock. Those 960 were never subsequently rerun under the canonical lock. Subsequent tranches resumed from 960 using the canonical lock. The scheduling disclosure records both lock identities and the unverified historical overlap.

The full ledger metadata check is portable. Full numerical regeneration of every inherited result remains incomplete as a standalone workflow. The historical scripts depend on workspace paths, dynamically selected intermediate files and execution order. Selected originals, the earlier ledger chain, all 82 parent-receipt artifacts, and the recorded marker-branch evidence are included. The original live 546 ledger changed during the audit. Its row contents were preserved in the v1 snapshot and a reconstruction. Its original byte hash and the reconstruction hash are recorded separately. See provenance.json for Git identities and the existing separately held archive.

Inventory chunks identify every payload by SHA-256. The ZIP SHA-256 binds the inventory chunks too. The official graph and fork helper are also available as pinned Git blobs. The optional-marker aggregate uses the recorded upstream audits. The new combined-ledger review checks their per-support coverage and evidence hashes.
