# Hidden-unit holdout

The complete baseline decided 28/28 correctly (16 SAT, 12 UNSAT). The independent selector route decided 12/28 correctly (6 SAT, 6 UNSAT) and explicitly declined 16 for lack of a block cover. Both routes received only n and the raw clauses. All 22 SAT witnesses independently replayed. No errors, timeouts or omissions.

| Family | Candidate decisions | Candidate declines |
|---|---:|---:|
| Sign-flipped implication rings | 0 | 8 |
| Two-anchor ternary parity recurrences | 8 | 0 |
| One-anchor ternary parity cycles | 4 | 0 |
| Random and parity-mixed 3CNFs | 0 | 8 |

Six SAT decisions reported projected unary, four UNSAT decisions unconditional empty data clause, and two UNSAT decisions affine contradiction. The public result exposes no original-variable unit list. The exhaustive oracle records all forced original literals for comparison; a projected unary count alone does not identify a forced original variable. On the satisfiable implication rings, precisely the k ring bits were forced, despite the candidate declining those cases. The eight random/mixed controls included two UNSAT cases, both mixed. Each SAT recurrence had exactly one model and each SAT parity cycle had two.

Total sequential subprocess time was 2.088 s for the complete baseline and 1.492 s for the candidate, which returned fewer decisions. Neither run reached a fallback search. The baseline decided 14 by fixed order, eight by unit propagation and six by unit propagation plus SCC. Every attempt, exposed work count, generation/oracle timing and raw witness is in results.jsonl. See protocol.md for the precommitment.

The reporting-only candidate revision 0cd93ea6 reproduced all 56 statuses and all original-model counts. The final replay used 1.452 s baseline and 1.448 s candidate. All six candidate SAT solutions had zero selectors after affine preprocessing. This holdout consequently supplies positive evidence for affine preprocessing but none for nontrivial selector component joins. results-first.jsonl contains the initial run on e6163c6f; results.jsonl contains the final replay.
