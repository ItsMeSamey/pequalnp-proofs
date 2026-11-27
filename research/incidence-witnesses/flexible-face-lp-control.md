# Exact flexible-tree congestion on six Fano circuits

The points and lines are indexed by integers modulo seven, with incidence p−l∈{0,1,3}. All six binary monotone circuits compute the full incidence predicate on all 16,384 inputs. For each of 21 proper-neighborhood faces we assign total probability one to eligible physical OR trees. The objective B is the largest summed probability of using any one physical OR outside J. Each case exempts the six most recently constructed scalar collector ORs. The choice of J is fixed, not optimized. Witnessed-switch extras are absent from this objective.

| Circuit | Gates | Different projected choices summed over faces | Choices per face | Exact B |
|---|---:|---:|---:|---:|
| Point stars, numeric query order | 27 | 42 | 2 | 5 |
| Point stars, matched noncherry | 27 | 42 | 2 | 9/2 |
| Line stars, numeric point order | 27 | 42 | 2 | 5 |
| Split all seven point stars | 34 | 1165 | 18–118 | 9/2 |
| Mixed point/line stars | 29 | 554 | 1–135 | 39/2 |
| Shared mixed pivot | 38 | 1895 | 8–365 | 22/5 |

All joins in the code are ordered left combs. In the matched case the query l=p is last in each point's three-query join, so the other two form a cherry and every query appears in two cherries. In the split case the first query's product is joined to a product containing the other two before the main collector. The hybrid computes point stars for the three points on line 0 and restricted line stars for all remaining edges. In the mixed pivot case, the fully specified circuit in the source uses a point-star donor clamped at two points and one line, two private arms of a shared g, and the auxiliary terms from near-minimum-common-marked-switch-negative.md. These latter two collectors have more than six ORs. Their larger or smaller B values concern their displayed exemptions; they do not bound the optimum over J.

## Exhaustion and exact certificates

Pin the two active points and two active queries on each face. Fold ones and identities, retaining IDs of surviving binary gates. For each of the ten free raws enumerate every possible physical path to the folded output. Take one path per raw subject to two compatibility conditions. A used physical node must have only one forward successor slot throughout the union, and a used AND may receive paths through at most one operand. These conditions are necessary for a tree after the forwarding of all ANDs. They are sufficient: fix the selected operand at each used AND, forward every other AND arbitrarily, and keep the indicated paths to the root. Contracting forwarded ANDs preserves the one-successor path union. A binary OR is a branch precisely when both of its slots occur in the union. Conversely each allowed forwarding and tree lifts to such a choice, retaining the path through each forwarded physical operand. The checker verifies nine distinct branch ORs in each resulting tree. Trees identical on the unexempt branch set give one LP column for that face.

The primal certificate assigns nonnegative mass to the enumerated face columns. The verifier checks each face sum, and computes the maximum physical OR load exactly. The dual certificate assigns nonnegative rational weights of total at most one to unexempt ORs. For each face the verifier minimizes the sum of the weights over its complete column list and adds the results. Equality with the displayed primal load establishes optimality. The JSON stores sparse rational certificates. Sorted face and gate-set order is fixed by the source. Solver output is used only to discover the certificate. Replay needs no LP solve.

Run in this directory with Python, NumPy and SciPy:

    timeout 14s bash -c 'ulimit -v 262144; export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1; python flexible-face-lp-control.py --replay'

The six-case replay completed in 1.2 seconds under this 256 MiB address-space limit. A separate exploratory edge-product DNF enumeration hit the memory limit; no value or bound for that case is reported. The experiment covers the specified topologies and exemptions only.
