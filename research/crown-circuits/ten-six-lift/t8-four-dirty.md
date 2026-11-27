# Eight-input threshold two with exactly four singleton-hot AND gates

There is no fan-in-two monotone circuit of size 19 computing threshold two on eight inputs with six AND gates of which exactly four accept a singleton. The signed-bank normalization, direct-input deletion and re-splitting, and minimum-size premise are those in t8-two-dirty.md and three-template-method.md. The general high-dirty-method.md records the chronological protected masks and the four-helper limit. A clean gate means an AND which rejects every singleton. This endpoint classifies one possible count of singleton-hot AND gates.

| Minimum protected helper cost | Chronological profiles | Orbit representatives | Banks visited | Semantic fronts |
|---:|---:|---:|---:|---:|
|0|154|34|20672518|1265936|
|1|1475|294|11309546|1024719|
|2|7236|1696|4674366|652195|
|3|23262|6777|1191017|222612|
|4|51800|19339|133999|28459|

All 28,140 representatives returned zero hits. Costs zero through three use t8-seeded.cpp. Cost four uses t8-fixed.cpp, and every bank counted there contains four paid protected helpers. The orbit-size column sums to 83,927. The two backends count visits according to their respective traversal, so bank totals describe computation. high-control.py exercises forward semantics on small positive full-cube controls for both hot-gate counts.

The compressed ledger is t8-4-profile-ledger.tsv.gz. Its decoded TSV has SHA-256 04d50653a2f84cde4047aefe8e42578289b904eb68ee0300c1deca90ce660490. Each row contains the 4 continuation masks followed by minimum helper cost, chronological orbit size, status, visited bank count and semantic front count. high-ledger.py matches each receipt to a distinct catalog key before producing this table.
