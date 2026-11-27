# Four receivers in the graph-9822 circuit scan

Take any well-wired binary monotone circuit on ten inputs with at most seventeen gates, exactly six AND gates and an in-range output. If it computes the graph edge function on all 1,024 Boolean assignments, exactly four of the ten receivers in its own scan satisfy RayValue. The statement has no reduced-circuit or hidden-gate premise.

The proof projects every possible three-receiver scan onto one of two finite families, then excludes both for all 38 retained ordered triples. Earlier kernel results restrict the count to three or four, so excluding three leaves four. Whether a size-seventeen circuit exists remains open.

SixD3OriginalFour9822.lean contains the two endpoint statements and their proofs. Run python verify_sources.py to verify the 731 source files, the external import manifest and the recorded Lean audit logs. The project archive stores each source at its module path. Both endpoints use propext, Classical.choice and Quot.sound.
