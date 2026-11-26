# Rank-seven proof layout

Use the ordinary basis order s,t,i,Z and the virtual q coordinate, with three independent ordinary contraction coordinates Z. The six local vectors are s,t,i and

    k = i+t+q+alpha,
    j = s+i+gamma*q+beta,
    l = s+i+t+(1+gamma)*q+delta.

Each of alpha, beta and delta is an arbitrary element of span Z. The displayed choice is the earlier chart with the basis element k replaced by t and the contraction tails renamed. The gauge makes the weights of s,t,i and the three Z columns zero; the remaining functional on q sets the weight of k to zero. The positive primal switch then specifies weights epsilon and 1+epsilon on j and l.

For a fixed pair (gamma,epsilon), three positive disjunctions require the presence of an admissible k, j and l respectively, each ranging over its eight tails. These choices are independent. Their three distinct non-tail projections ensure distinct ordinary occurrences. The formula may select additional such occurrences, as is permitted in the original ground set. Thus these are four unrestricted existence formulas, each covering 8³ labeled tail choices. The four-mode layout allows either order of the two peripheral weights. Its case count is separate from any enumeration modulo permutations of Z.

The common clauses use the rank-six hyperplane criterion in the new coordinates. All typed ordinary columns have presence variables. Mandatory s,i,Z carry weight zero. Distinguished t is handled separately. Forbidding either type of ordinary copy of t is safe in a stationary candidate: the fixed two-element supported cycle consisting of t and its copy is killed by every d with d(t)=0, and d(q) can vary because s,t,q are independent. A common primal cycle with two values of d(q) gives both mixed weights.

For each of the four formulas the mode selector was set true and its three negative selector literals dropped. Inactive modes can set their own selectors false, and add no constraint. The CNF is solved as a standalone file, with no solver assumptions, no induction splits, and no retained clauses from another mode. The checked all_tails.py has SHA-256 `6beb8ec468350c7721779c7153c06ab60499d70c666e232b214457a8228f47b8`.

Use `python -B verify_rank7_tails.py OUTPUT --drat-trim PATH` with python-sat and drat-trim to reproduce the four CNFs and traces. The optional `--mode 00`, `01`, `10` or `11` selects one formula. The two digits are gamma followed by epsilon.

All four unrestricted CNFs were refuted by CaDiCaL and independently verified with drat-trim. Each has 936 variables and 41,840 clauses. The [proof manifest](rank7-tails-proof-manifest.txt) lists mode, variables, clauses, DRAT lines, input and proof SHA-256 hashes, and checker result. The four hashes of each type were independently recomputed from the saved files. These certificates establish the stated conditional switch soundness through rank seven.
