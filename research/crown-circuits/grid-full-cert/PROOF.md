# The 29-gate grid prefix requires a 12-gate suffix

The twelve-crown has output 1 when the active row and column labels differ. Exactly one raw input is true on each side. Fix the 29 gates in `prefix.txt`. No suffix of at most 11 binary AND/OR gates computes the crown on all 144 promised inputs, even with unrestricted fanout and access to every raw or prefix wire. This result fixes those 29 gates.

The first twelve gates pair the two raw inputs at each label by OR. The other seventeen gates form three row-group and four column-group occupancy bits on the 3-by-4 grid. A 12-gate suffix tests whether at least two row groups or at least two column groups are occupied. Threshold two on three bits takes four gates by splitting off one bit. For four bits, compute the AND and OR of each pair, AND the pair ORs, then OR that result with both pair ANDs, using seven gates. The final OR brings the total to twelve.

Run `python3 verify.py` with Python 3.10 or later and a C++20 compiler named `c++`. The optional `--jobs N` sets the number of concurrent token-search subprocesses. The verifier checks the prefix hash, rebuilds the checkers in a temporary directory, and regenerates the source sets from the truth tables.

## Source sets

Replace any raw input used by the suffix with its paired prefix OR. On every positive assignment this can only increase the input to the suffix, and on each negative diagonal assignment its value stays the same. A correct monotone suffix therefore remains correct. The verifier checks these inequalities for each raw input. All 29 resulting source wires are ORs of paired labels.

Discard dead suffix gates. Constants, unary gates, and out-of-range reads interpreted as false can be simplified away. If a live binary circuit has $g$ gates and $s$ distinct source wires, its $2g$ input positions use every source and every nonoutput gate at least once. This leaves $g+1-s$ uses beyond the first. A completing suffix of at most eleven gates can therefore read at most twelve distinct sources. An output equal to a source uses one.

For every positive input $p$ and negative input $n$, some selected wire must be true on $p$ and false on $n$. The checker enumerates every source set meeting these differences. It retains the 24 inclusion-minimal differences, branches over the members of an unhit difference, and includes all affordable supersets of a solution. Disjoint unhit differences each require a different additional source. The resulting counts for 7 through 12 sources are 1, 30, 432, 3,929, 25,079, and 118,267. No smaller set qualifies.

For up to eleven sources the checker compares their bipartite incidence graphs, with distinct initial colors for labels and wires. Color refinement and individualization produce an ordered adjacency matrix. Equal matrices give an explicit permutation of labels and of selected source wires that preserves the full suffix problem. Skipping vertices in one block with identical neighborhoods only skips transposition symmetries. The twelve-source check runs directly on all 118,267 sets.

## Enumeration with copies

Starting with one token for each selected source, allocate at most $12-s$ extra copies. Copies of sources are chosen before the first gate. Each gate consumes two tokens and emits their AND or OR plus any desired copies within the remaining budget. Every live circuit appears in topological order by allocating each signal one token per downstream use. Unused copy budget is allowed. Tokens with the same truth table can be interchanged. Caching a failed multiset with its remaining budget preserves the search.

A proposed merge must retain a distinguisher for every positive-negative pair losing its last one or two distinguishing tokens. Also choose a completing suffix with the fewest gates among all normalized source sets. If the true diagonal cells of two AND inputs are nested, the operand true on fewer diagonal cells can replace their AND. This preserves all negatives and can only improve positives. For OR the dual replacement uses the operand true on more positive cells if those true sets are nested. These bypasses remove a gate and may remove sources. The enumeration includes smaller source sets, so a minimum counterexample cannot contain either gate.

With zero remaining copies, the continuation is a read-once formula in the current tokens. On a positive-negative pair let the positive input select a true child at each OR and the negative input select a false child at each AND, with deterministic tie breaking. Each leaf receives a Cartesian product of positive and negative inputs, and distinct leaves have disjoint products. A cell distinguished by just one token forces that token's rectangle to contain its row and its column. Overlap of two forced hulls excludes the formula.

## The eleven-source case

At most one signal can be reused. Without a repeated signal the read-once test applies immediately. If a signal is used twice, its inputs form a read-once subformula on a subset $S$ of the sources. The outer formula uses the remaining sources $T$ once each and the shared signal twice. A repeated source gives a singleton $S$. If $S$ is the full support, the outer function of the repeated bit is the identity or a constant, so the read-once test suffices.

On normalized wires a positive pair has the bitwise union of its two diagonal signatures. The checker retains inclusion-minimal positive signatures and inclusion-maximal negative signatures. These form a subset of the required tests. For every nonempty proper subset $S$, any cell lacking a distinguisher from $T$ requires the inner signal to be true on that positive input's $S$ projection and false on that negative input's projection. The checker tests all pairs of forced true and false projections for monotonicity and unique-leaf rectangle conflicts.

For the outer formula the repeated signal may distinguish a cell only if the positive projection lies below no forced false projection, the negative projection lies above no forced true projection, and an $S$-wire distinguishes the two projections. The checker permits the signal whenever these necessary conditions hold and imposes no unique-rectangle constraint on it. It checks the remaining cells for the ordinary unique-leaf conflicts on $T$. A conflict even under this relaxation excludes that split. This excludes every split in all 3,540 eleven-source isomorphism classes.

The token search handles the other source counts, including exact read-once search on twelve sources. The verified lower bound and the twelve-gate construction give an optimum suffix size of twelve for this prefix.
