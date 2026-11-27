# Chart dependencies for the 274-original review

The second independent review reconstructed 512 pivots on 274 original circuits. The table maps those pivots to the finite exclusions used in the proof. When a supplied input is unused, the proof uses the applicable single-input or literal chart. The review reran the original-input reconstruction and used the archived numerical chart exclusions.

| Supplied masks | Pivots | Physical inputs | Chart evidence |
|---|---:|---|---|
| None | fallback | Literals | [Literal chart](../literal26-novel102.sha256) |
| 9 | 222 | C129 | [C129](../c129-cap25-deltas.sha256) |
| 20 | 120 | C320 | [C320](../full-cap25-dispatch.sha256) |
| 9, 130 | 74 | C129 and C2052 | [Two-input chart](../pair9-130-3537-6176.sha256) |
| 9, 20 | 74 | C129 and C320 | [Source archive](../q2-two-complete.zip) |
| 9, 33 | 14 | C129 and C513 | [Source archive with nested numerical proof](../q2-129-513-lift.zip) |
| 20, 33 | 8 | C320 and C513 | [Source archive](../high-head-C320-C513-cap25-complete.zip) |

The last three rows share the [four-chart manifest](../four-chart-3566-6209.sha256). Run `sha256sum -c archives.sha256` from this directory to check the chart archives using repository-relative paths. The original independent checker records the producer's workspace paths. [Second review](review.md) · [Independent checker](check.py) · [Source archive](../allpresent-spine274.zip)
