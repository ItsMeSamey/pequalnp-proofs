# Enriched30 retained-prefix circuit bounds

This source release targets the 30-wire donor-bank decoder of the issued 32×32 graph fixture. The physical-cost theorem assumes a decoder realizes the target on all 1,024 care cells using AND/OR/NOT gates of arity at most two. The cost includes retained physical gates in the pinned source prefix. The original 170-gate fixture disagrees on 14 cells. The kernel audit covers seven endpoints. The retained-prefix floor is 182 without anchoring and 183 when the prefix also retains wire 69. Both bounds apply to the specified decoder interface.

Three top-level audit files cover the anchored, marker, and unanchored declarations. IMPORTS.json records their recursive source closure and SHA-256 pins, including the steward-selected pivot probe and nineteen two-fact chunk modules. The original generic distribution and its captured axiom audit are included in baseline/ and audit/. The active source tree follows the enriched kernel candidate, including the revised ForkWalk module. The vendored PEqualNP source, toolchain and package lock retain the upstream pins and license described in the generic distribution.

## Replays and kernel verification

Run these commands from the package root with Python 3.10+ and GNU coreutils. The enriched serializer regenerates its fixture-local Lean file.

    ./replay-fixtures
    (cd fixtures-enriched && sha256sum -c SHA256SUMS && python3 -IB serialize_enriched30.py && python3 -IB replay.py && sha256sum -c SHA256SUMS)
    cmp Enriched30Data.lean fixtures-enriched/Enriched30Data.lean

For Lean, use Elan with the enclosed lean-toolchain and Lake manifest. The first command fetches cached Mathlib build artifacts. With dependencies provisioned, build serially on memory-limited machines using the compiler scheduler's supported job-limit configuration.

    lake exe cache get
    lake build EnrichedCapacityRelease
    lake env lean Enriched30ActualCostAxioms.lean
    lake env lean EnrichedCapacityAxioms.lean
    lake env lean Enriched30UnanchoredCostAxioms.lean

## Fixture authorship and licensing

Team 01 supplied the cross-parent MUX seed. Team 07/r07 independently checked the physical seed. Team 09/w03 supplied the support certificate and enrichment; team 09/w02 supplied the chains and pivot formalization. Team 08/w07 wrote the serializer and independent fixture replay, and team 09/w09 contributed the retained census. The exact individual seed author and original ABC invocation are undocumented. Original support and generator bytes, including historical paths, are archived in fixture-originals/. Use fixtures-enriched/ for the portable replay and its detailed provenance. The upstream PEqualNP file carries the included Apache 2.0 license. Project-specific proof and fixture materials carry no separately supplied license grant.


## Audit evidence

All seven endpoint queries in the three audit drivers returned exactly propext, Classical.choice and Quot.sound. The captured outputs are in audit/*.expected. Compare fresh query output against its corresponding file. The source and object ledger confirms exact pairs for 22 of the 53 local modules, including all three endpoint audit drivers. For the remaining 31 modules the historical ledger lacks a complete source/object pair. IMPORTS.json and SHA256SUMS pin the shipped source bytes. An earlier pre-split launch of Enriched30Pivot used different bytes; its later successful matched pair is recorded separately. No redundant Lean build was run during packaging.

For an independent source-to-fixture binding, run the following from the release root.

    python3 -IB audit/verify_actual_cost_source_pins.py . > /tmp/enriched30-pins.json
    diff -u audit/actual-source-pins.json /tmp/enriched30-pins.json

The compiler steward's success ledger and captured receipt comparison accompany the final axiom output. The generic archive in baseline/ retains its own manifest. Run sha256sum -c SHA256SUMS after extraction.
