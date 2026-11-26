# Guarded DAGs of unbounded depth

Fix a topological order after substituting self-bit one in each guard. A zero bit is always legal. A one bit requires at least one true affine literal in its guard. Free inputs are leading vertices with constant-true guards. Substitute fixed inputs into the constants. First consider b single affine terminal equations. Store their coefficients on bit i as a b-bit label and absorb constants in the target.

## Rank of future guard responses

At a cut after i bits form the matrix M_i whose rows are the masks of all guard literal occurrences at still-unprocessed vertices, restricted to the processed prefix. Define r as the maximum binary rank of these matrices over cuts. This depends on the supplied order. Gaussian elimination at each cut computes r in polynomial time if desired.

A prefix assignment x contributes M_i x to future literal truth values and one partial b-bit terminal syndrome. Keep one witness prefix per pair. For a proposed bit 1, use the entries of the response vector belonging to its guard, adding the respective literal constants, and require some true entry. A proposed bit 0 is always admissible. Delete the current guard rows and add the new column times the chosen bit to the remaining responses. Add its label times the bit to the syndrome. Prefixes with the same pair admit exactly the same valid completions and have identical completed syndromes under any common completion. This proves correctness by induction. At most 2^(r+b) states occur per cut, even if the implementation stores full response vectors. Deterministic time and space are 2^(r+b) poly(input size), using e.g. sorting for deduplication or the supplied integer-key dictionaries (even quadratic collision overhead still gives single-exponential time). The pair keys in the implementation use tuples; the deterministic worst-case time with Python dictionaries is 2^O(r+b) poly(input size).

For example, if every guard depends on one affine parity of all earlier bits with identical coefficients on their common prefix, the future matrix has rank at most one, while depth and individual guard width can both grow linearly. More generally, interval parity dependencies spanning a cut have rows that are suffix indicators of the prefix. Their rank equals the number of distinct nonempty suffixes, regardless of the number of such requests.

## Arbitrary unary dependency forests

If each guard depends on at most one earlier bit, the dependency graph is a rooted forest, with no bound on its height or branching. Tabulate the attainable subtree label sums conditioned on the value of the parent. For each locally legal value v, start with its own label contribution, merge the child tables for parent value v by pairwise XOR, and retain one witness per sum. Union over legal v. Merge roots by the same operation. Subtrees are disjoint and communicate only through the selected parent value, proving exactness. There are at most 2^b sums per table and O(n) binary merges for each of the two local values, giving O(n 4^b) pairs and polynomial witness-accounting overhead. No cut-rank bound or special vertex order beyond parent-first is required.

For b terminal disjunctions, apply the deterministic selector projection in [the affine projection note](../clause-projection.md). It changes only the terminal labels, preserving both the guard rank profile and unary forest. This gives 2^O(r+b) poly(input size) and 2^O(b) poly(input size), respectively. Each projected witness also satisfies the original terminals.

Run python test_solver.py in this directory. It checks 500 seeded small instances against exhaustive validity and syndrome evaluation on every three-bit target, plus two depth-1000 examples including a dense rank-one guard matrix.
