# The complete 21-mixed width grid

All primary proofs and replays completed. Fresh independent price-nine runs are tracked in status.md. Every residual separator of total size ≤33 requires ≥22 mixed gates. This leaves unrestricted existence open.

All paths are relative to /workspace/scratch. SHA256SUMS pins the listed packages, proof entry points and loose frontier code. The original sample is bundled with the principal checkers. Apply the previous ≥21 bound indexed by synthesis_new/twenty-summary/README.md first. At 21 mixed and total≤33 the pure budget is 12, point width P≥11, line width L≥7 and the surplus is 22−P−L. The grid and pre-filter prices are in syn_bounds/twenty-one/README.md, whose intermediate status table predates the final cases.

| P | L | Surplus | Exclusion and replay |
|---:|---:|---:|---|
| 11 | 7 | 4 | synthesis_new/seven-four/README.md; syn_dual/eight-three-certificate.zip for component charges; syn_mitm/seven-line-k3.zip, syn_mitm/eight-two/raw-triple.zip and syn_mitm/eight-two/seven-four-basic.zip. Final two banks both fail twelve-bit minors. |
| 11 | 8 | 3 | syn_bounds/twenty-one/point-equality-frontier for price 9 and 1,070 ≤10 local geometries. Nonlocal ≤10 floor in synthesis_new/nonlocal-seven/README.md and synthesis_new/twenty-summary/nine-lines.md. At 11 paid only a physical pair fits; syn_dual/eight-three-certificate.zip excludes nonlocal cases and syn_mitm/eight-three/fixed-star-local-marks-only.zip certifies 2,668 local banks via root role reduction. |
| 11 | 9 | 2 | Same equality frontier: 2,604 price-nine and 8,466 ten-paid local joint geometries; same nonlocal ≤10 floor. |
| 11 | 10 | 1 | Same equality frontier: only nine point gates fit, 27 banks by 8,275 line multisets giving 9,938 simultaneous geometries. |
| 12 | 7 | 3 | syn_mitm/seven-line-k3.zip. |
| 12 | 8 | 2 | syn_quotients/w12_k2_cert.zip and syn_mitm/twelve-eight/w12-l8-expensive.zip; see detailed prices below. |
| 12 | 9 | 1 | syn_quotients/w12_module_cert.zip at point prices ≤9. Price 10 falls to syn_quotients/w12_low_cert.zip, w12_zero_cert.zip, w12_roles_cert.zip and w12_two_masks.zip in that same directory. |
| 12 | 10 | 0 | syn_cover/twelve_ten/W12L10-verified.zip: 345,810,125 comparisons. |
| 13 | 7,8,9 | 2,1,0 | syn_mitm/seven-line-k3.zip; eight-line reconstruction in syn_dual/eightplus/README.md and synthesis_new/nineteen-final/README.md; nine-line reductions in synthesis_new/twenty-summary/nine-readonce.md with syn_quotients/fourgroups11_w13.zip. |
| 14 | 7,8 | 1,0 | Same seven/eight-line occurrence bounds. |
| 15 | 7 | 0 | Same seven-line bound. |

P11,L11 exceeds the pure budget, requiring at least nine point and four line gates. Greater values of P+L exceed the tree limit.

For W12/L8 and point price≤8 the repeat-inclusive run compares 450 favorable point banks with all 128 eighth signatures (16,764 simultaneous orbits). At price nine the mask has at most four members. Up to three, the geometric pair/triple role proof also admits price nine; for size four all 305,306 joint orbits pass to empty via the recursive two-cut module. A repeated point boundary unfolds into the W13/L8 one-surplus theorem; a repeated line unfolds into the W12/L9 cost-nine theorem. At point cost ten the mask is a pair or triple, and at eleven a pair. The expensive archive covers the 732,43,46 and 2,817 final role domains. Zero/duplicates reduce to seven lines, including the degenerate cost-twelve possibility.

See the README in each archive for its runner. The loose equality-frontier commands are python verify.py 11/8 11/9 11/10 and python local_ten.py 8 9. Some older upstream proof inputs are listed within their geometry/charging entry points. Keep separate extraction and scratch directories for independent replays.
Alternate W12/L8 price-nine proof: all 865,746/865,746 orbits, including the 560,440 masks of support at most three, fail. Run python verify_all.py 9 in syn_quotients/w12_k2_all.zip; no expensive geometric transfer is needed for this alternate.
