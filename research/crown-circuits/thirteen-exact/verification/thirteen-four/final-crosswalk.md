# Four-pure coverage at size 31 with seven ANDs

Run python3 final_crosswalk.py from any directory. It checks the 351 distinct six-column rows from quartet_models.cpp with arguments 7 4 (the decorated rows are emitted on stderr). The four disjoint classes are as follows.

* 195 contain a degree-four flag and a branching pure triple. Apply ../../degree/t13-seven/inherited-quartet.md, which uses the independently reviewed ten-quartet-hosts.md and ten-no-quartet.md in that directory.
* 80 contain four pure triples and have three or four branches. Apply final-exit-count.md. Its degree-three bound for all mixed flags uses inherited-quartet.md. Its support prerequisites are the thirteen-input seven-AND census, shared-eight.md and five-three-three-terminals.md in degree/t13-seven. The argument applies on all pure graphs.
* 14 have four quartets forming a triangle and an isolated vertex (graph mask 52). Apply quartet-triangle.md. That note was originally used on nine rows after a previous star cut, but its proof uses just this graph, plus the pure-quartet fanout, private partner and nine-input composition premises, independently of the branching mask. The other five rows also fail the existing star cutoff in cuts.py.
* 62 have two private clean triples. Run clean2.py from this directory and compare its output to clean2.log; see README.md for the OR-injection and truth-table overgrant. The final crosswalk verifies that the uncovered rows are exactly the 62 logged members.

The crosswalk is a subsecond Python check. The complete two-clean solver is a separate finite calculation. A frozen independent CNF/DRAT replay is available in restricted-drat.jsonl and drat-certificates.tar.gz; use replay_clean.py with clean2.log to select these two-clean rows, or clean2.py for the primary replay. The final crosswalk does not use any p3-to-p4 transfer, promotion assignments, the one-clean SAT screen or a host completion census.
