# Minimal connected native failure of full protection with separated roots

On sockets 0 through 5 use fixed feedback (2 3 4 5), fixing 0 and 1. Apply the two independently optional rotations (0 3 2) and (1 5 4) before feedback. Their socket triples meet a single feedback cycle, so the untied network is connected. Complete direct enumeration gives

| Active gates | Orbits |
|---|---|
| neither | (0), (1), (2 3 4 5) |
| first | (0 4 5 2), (1), (3) |
| second | (0), (1 2 3 4), (5) |
| both | (0 4 1 2), (3), (5) |

The pairs separated on all four masks are exactly {0,3} and {1,5}. Thus the roots 1 and 5 never meet, even though the fixed count of three is not protected by any three marks. Passive subdivisions merely duplicate observations of the original fixed wires, so they cannot supply a missing third orbit representative.

Two gates are minimal among connected native networks, allowing arbitrary fixed reversible feedback. If there are at most two orbits, a permanently separated pair itself supplies a full marking whenever that pair exists. A connected one-gate network, after suppressing passive wires, is a permutation of just three sockets; count three at baseline forces identity feedback, and the active gate then merges the three orbits. A connected zero-gate network has just one orbit.

## Necessity of multiple caps when cycle count is unchecked

On three sockets let feedback be identity, the single optional rotation be τ=(0 1 2), and mark all three sockets. The original orbit counts are three and one. Capping once by τ gives the permutations τ and τ², both single tours. The inverse cap instead gives τ⁻¹ and identity, exposing the failing mask. The fixed-count single-cap shortcut therefore requires its stated hypothesis.

Run check_unprotected_separation.py and verify its recorded SHA-256 in unprotected-separation.sha256.
