# Enriched30 fixture provenance

The target is the graph in the issued L-meta-20579 statement. Cell 32r+c encodes row r and column c. The physical circuit takes one-hot row bits followed by one-hot column bits. Its 170 gates disagree with the issued graph on 14 cells. Witness signs use issued graph labels.

| Contributor ID | Role |
| --- | --- |
| site-team-01 | Supplied the candidate through its ABC drafts as fresh-mux-170-14.json. source-circuit.json preserves those bytes. The fixture does not record the individual circuit author or exact ABC invocation. |
| site-team-09 | Supplied the pinned circuit, full bank, last14-support-certificate.json and enriched30-chains.json. The latter two reports supply the native cell pairs. support.json normalizes the source path and JSON layout. chains.json preserves the original bytes. |
| site-team-08/w07 | Wrote the serializer, checked donor orientation and labels, wrote the independent integer-bitset replay, and verified byte-identical regeneration. |
| site-team-09/w02 | Consumes the generated definitions for the physical assignment and pivot formalization. |
| site-team-08/w04 | Packages the release. Compiler and proof verification status belong to the enclosing release. |

For wire 89, cells 326 to 336 witness a rise and 388 to 67 witness a fall. Cells 11 and 815 differ on both wires 89 and 90.

## Host replay

Use Python 3.10 or later with its standard library. Run these commands from a copy of this directory. The serializer writes beside itself. The replay reads the emitted Lean literals and evaluates all 1,024 cells as integer bitsets. It verifies physical gates against the source, target rows against the issued statement, and all singleton witnesses against the full bank.

    sha256sum -c SHA256SUMS
    python3 serialize_enriched30.py
    python3 replay.py
    sha256sum -c SHA256SUMS

Expected fixture SHA-256 is 06f1881c98971698b527d7b3ce2220011ccc6407fc450a14984bb8c03aa47c30. Host replay verifies the concrete data. The release steward handles Lean compilation.
