# Five pure groups with two branching groups

A regular minimum circuit for thirteen-input threshold two with 31 gates and seven AND gates cannot have exactly five pure groups of which two branch. The result uses structural and finite lower bounds for smaller threshold circuits.

The graph enumerator produces 608 decorated instances before permutation deduplication. A pure quartet disjoint from a branching triple survives deletion of that triple into the forbidden ten-input, 24-gate, seven-AND quartet configuration. This removes 289 instances. For each quartet remaining, the hereditary component bound requires at least two pure vertices outside its pure component. This removes another 15 instances. The 304 survivors have no quartet and no dirty private product.

The certificate for all clean-private instances uses private-partner order and singleton support bounds, followed by the disjoint two-injection prefix argument in clean-prefix.md. The 22 final problems in chains-fast.log exhaust this larger family. All 56,686 canonical arm assignments were rejected. These two calculations cover the stratum without invoking a partial dirty-case search.

Run crosswalk.py to verify the two graph cuts and historical residual ledger. Run replay.py to regenerate the original graph table, check it byte for byte, check the crosswalk, and compare the entire clean-private computation against its frozen ledger. The historical directory contains the earlier 29 one-dirty and 44 two-dirty records and their identifiers. Every one directly exhibits a quartet disjoint from a branching triple.

The assumptions directory includes the inherited-quartet lemma, the ten-input quartet exclusion, and the decoder layer proof. Each note states its prerequisites. The enumeration and the clean-private reduction also use the project's raw-reader and OR-group normalization, pure-group census, private probes and ten-input gate composition. This is a mathematical and computational result. A Lean kernel proof remains open.
