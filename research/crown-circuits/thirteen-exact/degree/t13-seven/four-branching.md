# Six pure groups and four branching groups

The six pure groups include four branching groups and two private groups U and V. Each private group supplies a single dedicated AND whose other operand is called its partner. Write d for the number of dirty dedicated ANDs. The physical surplus, dirty hot witnesses, directed probes and group classifications are described in six-pure.md and private-probes.md. Starting from all six-group geometries, b4_coverage.py applies those necessary conditions. After sorting indistinguishable labels, the full layout counts are as follows.

| Dirty dedicated ANDs | Distinct partners | Common partner |
|---|---:|---:|
| 0 | 1199 | The two clean products factor |
| 1 | 402 | 7 |
| 2 | 24 | 0 |

## Gate budget on a restriction

Retain every label incident to two pure groups and up to two selected labels with at least one mixed incidence. Set all other raws to zero. The four branching group outputs can be supplied directly. Each private group disjunction is available only as its dedicated AND operand. A mixed OR group has at least one nonraw operand. If it has u nonraw operands, it uses u−1 ordinary ORs, plus a raw injection for each retained raw incidence. Summing u−1 over the mixed groups gives four. Each marked injection is an OR with its specified raw input. After restriction this computation accounts for all OR gates outside the pure groups. Each of the thirteen singleton supports determines the value of both partners on the retained inputs. Every retained singleton must be rejected, and every pair of distinct retained labels must be accepted.

Each clean dedicated AND is a terminal in the clean-terminal representative. If there are c clean dedicated ANDs, reserve c ordinary ORs in the final collector. Another terminal exists because two labels outside U and V form a positive pair with both dedicated products false. Reassociate all other terminals as one signal F. Reassociation changes no gate count. Every reserved OR has two nonraw operands. No collector OR or clean product is needed to compute the remaining signals after reassociation.

Consequently there are 4−c ordinary binary OR slots, one marked slot per retained mixed incidence, and d dedicated dirty AND slots. Grant arbitrary conjunctions, constants, and unrestricted fanout. A wire between slots is now a conjunction of some previous slot outputs and freely accessible branching group indicators, or false. Enumerate these factors using selection variables shared across the tests. A marked injection supplies its specified raw OR the preceding conjunction. A dirty private slot computes its known group disjunction AND a selected partner expression. Clean partners and F may use any earlier slot. The final value is F OR the clean dedicated products. The common-partner encoder grants the full four ordinary OR slots without reserving a collector, and enforces equality of both partner taps on every tested input. All formulas include an explicit constant-false selection. A SAT obstruction therefore also excludes the original circuit.

The two-clean and one-clean ledgers list a concrete raw restriction for every full layout. The checkers permute the four freely branching inputs and permute retained mixed labels. The private pair can swap only when both are clean. An independent DRAT checker reads each generated CNF and proof. The two-dirty/distinct and one-dirty/common cases use six and five restrictions respectively. The full census and individual proof logs are separate so their status can be verified independently.

Run b4_coverage.py with a temporary directory. Run clean_certs.py with clean-restrictions.jsonl.gz, a temporary directory, and the drat-trim executable. Run it again with one-clean-restrictions.jsonl.gz and a fourth argument dirty. These regenerate 286 and 58 distinct formulas. Run common_replay.py and two_dirty_replay.py with the drat-trim executable followed by a temporary directory to regenerate the other five and six formulas, respectively. Every reported digest is taken only after drat-trim verifies its refutation.
