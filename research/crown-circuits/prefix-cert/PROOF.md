# An obstruction for a fixed 29-gate prefix of the 12-crown

**Claim.** No suffix of at most 11 binary monotone AND/OR gates completes the circuit in `prefix.txt` to the 12-crown. Each suffix gate may read either side's raw inputs, any prefix wire, or any earlier suffix wire, with unrestricted fanout. On a promised input exactly one of the 12 row inputs and one of the 12 column inputs is true. The desired output is true precisely when their indices differ.

Run `python3 verify.py` using Python 3.10 or later. The checker reads its adjacent prefix and uses the standard library. Each prefix line specifies an operation (0 for OR, 1 for AND) and two earlier wire indices. Raw wires occupy indices 0 through 23, with the row inputs first.

## Bounding the number of sources

Retain only gates reaching the output. Constant and unary gates can be simplified, so permitting them gives the same exclusion. Let the suffix use $g$ binary gates and $s$ distinct source wires from the 53 raw and prefix wires. There are $2g$ incoming edges at suffix gates. Each source and each nonoutput live gate must feed at least one input position. This accounts for $s+g-1$ edges. The number of excess uses is $g+1-s$, counting two uses at one gate separately. An output selected directly from a source has only one source.

Every positive assignment $p$ and negative assignment $n$ must differ on some selected wire with value 1 on $p$ and 0 on $n$, by monotonicity. The verifier evaluates all 144 promised inputs and enumerates the source sets hitting every such difference. After retaining inclusion-minimal differences there are 42 constraints. The search branches on all members of an unhit constraint and prunes only when disjoint unhit constraints require too many additional sources. It includes every superset of every completed branch up to size 12. There are two feasible sets of size 11 and 118 of size 12.

## A necessary rectangle test

For a read-once monotone formula, give one player a positive assignment and the other a negative assignment. At an OR, the first player chooses a true child. At an AND, the second chooses a false child. Fix a deterministic tie rule. The assignment pairs reaching each leaf form a rectangle, a product of a row set and a column set, and the leaf wire distinguishes every pair in its rectangle. Each wire has at most one such rectangle if it occurs once.

For each cell the verifier lists all available distinguishing wires. A cell with one choice forces that wire. Given forced cells for the same wire, their row-by-column hull is also forced. Propagate until a contradiction or a fixed point. A contradiction excludes the formula. Keeping only minimal positive and maximal negative projected assignments selects a subset of tests that every candidate must pass. All 120 possible supports contradict the read-once condition.

## The sole possible repeated signal

With 12 sources there are no excess uses. With 11 sources there is at most one. If it exists, one signal feeds two positions. All other live gates and sources feed one each. Thus the signals computing the repeated value form a read-once subformula on a source set $S$, disjoint from the sources $T$ in the outer formula. A repeated raw input gives a singleton $S$. The outer formula is read-once in the sources in $T$, with two occurrences of the repeated value. If $S$ is the full support, the output depends only on that one Boolean value and the nonconstant monotone outer function is the identity. The read-once check already covers that case.

For each nonempty proper $S$, a pair lacking a distinguishing $T$-wire forces the inner function to be true on the positive projection to $S$ and false on the negative projection. Apply the rectangle test to all pairs of these forced true and false projections. When it passes, test the outer formula. A shared-value leaf can distinguish a pair only if its positive projection lies below no forced false projection, its negative projection lies above no forced true projection, and the positive projection has a distinguishing $S$-wire. The verifier permits a shared-value marker whenever these necessary conditions hold and imposes no rectangle constraints on the marker. It enforces the unique-rectangle condition on every $T$-wire. A contradiction in this relaxation excludes the outer formula.

Each 11-source set has 2,046 nonempty proper subsets. For one set the inner and outer checks exclude 2,026 and 20 cases, respectively. For the other they exclude 1,957 and 89. This exhausts the live suffix shapes for the supplied prefix.
