# Hidden selectors after physical compilation

Of 28 precommitted compiled sources, the selector solver decided 20 correctly and declined eight. There were ten SAT and ten UNSAT decisions. Every SAT model passed checks on the permuted physical CNF, the original physical CNF after reversing the ID permutation, and the untouched source after decoding. No source coordinates were passed into the solver.

| Source family | Compiled decisions | Projected join |
|---|---:|---|
| Signed implication rings | 8/8 | 7 majority, 1 meet |
| Anchored ternary parity recurrences | 8/8 | affine |
| One-anchor ternary parity cycles | 4/4 | affine |
| Random and mixed | 0/8 | unrecognized; declined |

Every decisive query retained 6–10 selectors. The parity cycles have nonempty individual scope relations even when the global charge is inconsistent. Both inconsistent cycles were rejected by the projected affine join. This demonstrates global affine composition in this implementation. Exhaustive source models certify the recorded original units; decoded SAT witnesses are not certificates that those values are forced.

Compilation produced 360–2,349 physical variables per case. Totals across 28 cases were 37,740 physical variables, 125,660 clauses and 354,964 literals. Compilation took 0.250 s and relabeling 0.362 s, inside 5.425 s total sequential subprocess time. The solver reported 288,400 cells, 5,472 component probes, 214 traceback probes and zero fallback evaluations. No timeouts or omissions. All eight declined cases were checked by exhaustive source enumeration. No exponential physical enumeration was attempted. This is a compiler-derived benchmark; the original raw 28-case experiment remains separately reported.
