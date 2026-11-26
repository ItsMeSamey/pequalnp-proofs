# Forced graph restrictions

For each projected bank with only weight-two minimal positives, list its fifteen positive edges. A Boolean assignment is forced negative exactly when it lies below at least one recorded negative. Each of the graphs has 32 maximal independent sets. The negative cover counts for banks 0, 2, 3, 4, 5, 6 are 18, 18, 18, 15, 20, 16. Therefore none of the six samples forces the total graph function. If all variables outside S are set to zero, the full graph function on S is forced precisely when no missing independent set is contained in S. The exhaustive subset check in graph-minors.py gives the maxima below.

| Banks | Largest number of remaining vertices | Largest number of remaining edges |
|---|---:|---:|
| 0, 3, 4 | 9 | 7 |
| 2, 5, 6 | 10 | 8 |

The ternary restriction search elim.cpp also allows fixing variables to one. Its basic gate-elimination lower bound uses essential variables and first-gate canalization. Given a first gate on i,j feeding a later output, fixing either operand to its canalizing value removes this gate and at least one successor; the neutral value removes at least the gate itself. A lower bound of at least two, inherited from a restriction or witnessed by essential coordinates, excludes a one-gate output before invoking this rule. The resulting unconditional lower bound is only 13 on the two total graph types; hence this argument alone cannot resolve their 18-gate partial instances.

A general statement that total C4-free graphs require |E|+τ−1 unrestricted monotone gates would substantially exceed the unrestricted Boolean bounds discussed in Remark 10 of Jukna's *Lower bounds for tropical circuits and dynamic programs*. The rectangle proof in this directory uses the stipulated single product level.
