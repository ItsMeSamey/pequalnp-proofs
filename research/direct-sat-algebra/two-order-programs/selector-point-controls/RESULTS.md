# Precommitted comparison

All six original sources were decided by point_solver.py 31019302. Each positive raw word passed the original signed clauses and selected exactly the designated middle vertex in all three colors. For each h the original FD clock with cap 256 skipped at bank zero with zero binary probes, and point codimension cap 2 skipped with zero transition calls and closure seeds. Endpoint charges and the fully moving future selectors were included throughout.

| vertices per color | frontier, c, d at bank zero | result | transition calls | seed subsets | max retained | end-to-end ms |
|---:|---|---|---:|---:|---:|---:|
|3|15,9,3|UNSAT|220|859|7|9.86|
|3|15,9,3|SAT|218|521|8|7.27|
|5|21,15,3|UNSAT|382|2205|7|20.14|
|5|21,15,3|SAT|386|1303|8|20.25|
|9|33,27,3|UNSAT|706|7765|7|122.05|
|9|33,27,3|SAT|722|4308|8|81.27|

Times are single-run solver wall times, including the preflight; preprocessing is not separately instrumented. All 18 dispatches, cost vectors and raw witnesses are in results.jsonl (SHA-256 a6c9b178a5c4594fe68a8f6e3f1addbe21b6e4349bd556f84e3505ceafc0f582). The six isolated serial Python children used 0.5774 aggregate CPU seconds including interpreter startup and all three dispatches per case. No resource cutoff occurred. The original precommit is cdeeb867. The controls are also solvable by direct fixed-color enumeration, or by telescoping the carry equalities and one parity-constrained binary solve, so the comparison establishes a difference of implemented structural guarantees rather than a new SAT tractability class.
