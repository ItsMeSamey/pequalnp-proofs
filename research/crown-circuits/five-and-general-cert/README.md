# Five AND gates do not suffice for a 40-gate 12-crown

A monotone binary circuit with exactly five AND gates cannot represent inequality on twelve labels using at most 40 total gates. The 12-crown input has one active row port and one active column port. The separate four-AND certificate excludes smaller AND budgets. This result leaves six or more AND gates open. As a consequence, threshold two on twelve input bits has minimum size 29 among circuits with at most five AND gates: the checked control attains 29.

## Proof route

1. Resolve the five AND gates by their 32 direction choices and transpose. There are at most 17 binary unions. Each receiver mask rejects its own label on at least one direction. A row and column of different labels have full union on all directions. Comparable twins may both use their larger receiver mask.
2. A circuit without a raw receiver equal to an existing split branch can be paired without increasing size. The argument applies for any number of AND gates and is independently audited in crosscheck/no-direct-pairing-audit.md. See asymmetric/no-direct-pairing.md.
3. If a raw receiver equals a branch and three or more incomparable pairs remain, then there are at most three nonreceiver helper unions. The other shore's eleven receivers must cover the entire opposite half-cube. The direct-receiver compatibility test rules out all families of up to three helpers. Its independent execution returned 27 relative cube shapes, 18,354 reachable auxiliary families, and zero survivors. See the last section of asymmetric/five-four-and-three-defects.md. At most two incomparable pairs always permit pairing by opposite shore choices. The additional four-defect calculation has 284 direct and 58 indirect UNSAT cases replayed using DRAT.
4. A paired candidate induces a circuit with at most 28 gates computing twelve-input threshold two. Observing a matching pair at the same reverse signal allows its input OR to be shared, then replaced by a single variable in the tail. Monotonicity extends the prescribed singleton and pair values to the full cube. Conversely, each eleven-variable minor and each positive control is checked on the full Boolean function.
5. A paired direct receiver gives an eleven-variable threshold circuit of at most 25 gates and four AND gates, which the eleven-variable certificate excludes. The supplied eleven-variable upper control has 27 gates and four ANDs, passes all 2,048 inputs, and is SAT in both verification solvers. See paired/eleven-threshold-and-direct.md.
6. In the remaining paired case all twelve receivers cost unions. At most five nonreceiver masks can be paid, including every nonbase activated mask W. In a minimum-dirty counterexample no dirty W can equal or contain a receiver. Enumerate all 617 signed-permutation selector profiles and all feasible helper libraries, checking for twelve nonempty pairwise disjoint receiver deficits. See paired/paired-five-helper-search.md and paired/coverage.tsv. The generic oracle returned zero witnesses for each of the 617 profiles. Its complete per-profile counts are in paired/census.tsv. The broader scoped census results in crosscheck/ also confirm their respective subsets.

The result is a mathematical proof with finite executable enumeration and SAT checks. The files do not provide a Lean proof of the full five-AND result.

## Reproduction

Use a C++20 compiler, Python 3, python-sat with CaDiCaL and Glucose, and optionally drat-trim. Set DRAT_TRIM to the executable path when it is not on PATH.

From asymmetric run the following two commands.

    c++ -O3 -std=c++20 covercompatible.cpp -o covercompatible
    ./covercompatible > replay.out 2> replay.log

The result has no stdout and the log matches covercompatible.log. The matching-only comparison is reproducible with coverfamilies.cpp. The optional four-defect DRAT checks run with python four_defect_drat.py direct and python four_defect_drat.py indirect.

From paired run the following commands.

    c++ -O3 -std=c++20 fiveprofiles.cpp -o profiles
    c++ -O3 -std=c++20 canonicalfive.cpp -o canonical
    c++ -O3 -std=c++20 exact_five_helpers.cpp -o helpers
    ./profiles | ./canonical > replay-profiles.out
    cmp replay-profiles.out canonfive.out
    ./helpers 0 5 < replay-profiles.out > replay-census.out
    c++ -O3 -std=c++20 specific_bank.cpp -o positive
    ./positive < five-flat-control.txt
    python eleven_replay.py

All 617 entries in a complete helper run should have zero in column two; the positive-control helper run returns acceptance with six helpers. The full profile census is more computationally intensive than the positive controls. The eleven-input initial enumeration is reproducible by compiling eleven_budget.cpp and comparing its stdout against eleven_budget.out.
