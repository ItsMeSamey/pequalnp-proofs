# Independent domain review for W12/L9 at mixed count 23

The reviewed archive m23-w12-nine-complete.zip has SHA-256 04174837f321de9b9caeb72b3c084852019b333110164731657808cc3dfbc85f. Its nested point-price certificate twelve-eight.zip is byte-identical to the previously checked archive. The minimum of each point-bank orbit under sample automorphisms is a sound grant even when some orientations have a more expensive physical implementation. The 2,767 paid point banks produce 2, 5, 25 and 119 point orbits of respective minimum cost 5, 6, 7 and 8. A nine-wire physical line boundary needs at least two gates in addition to the seven raw labels, so these four prices exhaust the ten-gate pure budget.

A direct SAT model uses a Boolean presence variable for each of the 127 nonzero line masks. For each raw positive-negative comparison where the negative includes the positive point, at least one selected mask must contain the positive line and avoid all negative lines. These conditions give 303 distinct clauses. With at most nine selected masks and at least one omitted raw label, all 24 SAT solutions use nine distinct masks, and the exact 24 coincide with the packaged exceptional list. Every remaining line bank therefore contains all seven raw singleton signatures, leaving two freely repeated masks, including zero.

Deduplicate gate-output singleton signatures in topological order, and replace zero outputs by false. Each excess occurrence in the physical bank costs at least one such deleted gate. The remaining computation with two intersecting rich masks has a connected dependency cone on at least the size of their union in raw labels. This needs at least union size minus one gates. For disjoint masks their two cones have at most two components, giving union size minus two. With one rich mask the ordinary connected-cone bound applies. Each exceptional bank already requires three distinct nonraw outputs. Checking every line bank against an independent cost calculation gives physical price counts 540, 1,529, 2,590, 2,527, 1,085 and 9, at costs 2 through 7 respectively.

| Point cost | Maximum line cost | Initial relaxed pairs | Pairs at physical line price |
|---:|---:|---:|---:|
| 5 | 5 | 2,414 | 2,378 |
| 6 | 4 | 11,841 | 11,347 |
| 7 | 3 | 41,513 | 35,964 |
| 8 | 2 | 84,460 | 53,377 |

The physical paired sets were separately generated through the earlier W12/L8 raw-sample automorphism code and matched the packaged domain after applying physical line costs. The primary ordered-region and exact-partition results are separate from this domain audit. A fresh complete bulk replay is recorded below.

To rerun, let W9 be the extracted w12-nine directory and W8 the extracted w12-l8-m23 directory. Run `python line_domain.py W9`, then `python W9/cases.py DOMAIN` in a writable directory, followed by `python geometry.py W9 DOMAIN W8`. The geometry comparison recomputes all four sets rather than comparing only their cardinalities.
A fresh extraction of the sealed archive ran unmodified verify.py sequentially at all four prices and exited successfully. The exact stage rejected 0, 384, 2,400 and 57,154 partitions, respectively, totalling 59,938. All uncapped partition searches completed. The four fresh-replay logs record all stage counts.
