# Two original starred edges in L-meta-6648

Under the issued least TopForm G11 circuit and selected-set hypotheses, assume the original starred edge set has cardinality s=2. Then U=14≤j+2c+q. By the issued balance |X|+j=U+|J|, this proves |X|≤2c+|J|+q on this entire stratum. The result concerns the original star set, including both adjacent and disjoint pairs, with arbitrary issued j≥3, c≥0 and q≥0.

Put P=j+2c+q. If P≥14 the result follows directly. Otherwise the original normalized size count is P+2t+l=22 and P≤13. In particular q≥11 is already excluded from failure. Use the following exhaustive dispatch for a hypothetical failure.

| Original regime | Justification |
|---|---|
| q=0 | Accepted L-meta-18392 in its U≥3 regime; here U=14. |
| q=1,2,3 | Previously reviewed whole-q results, identified in PRIOR.md. |
| c≥1 and q≥4 | Since j≥3 and P≤13 one has q≤8; premises_6648_s2_cpositive_complete.md handles both star shapes and all such j,c. Its two supporting lemmas are included. |
| c=0, q≥4, adjacent stars | 6648-adjacent-stars-all-j-cover.md applies to every j and P≤13. |
| c=0, q≥4, disjoint stars, j=3 | Previously deposited 6648-two-disjoint-stars-three-junk.md covers every q. |
| c=0, q≥4, disjoint stars, j=4 | 6648-two-disjoint-stars-four-junk.md covers every q. |
| c=0, q≥4, disjoint stars, j≥5 | P≤13 gives q≤8. For q≤7 use 6648-disjoint-stars-low-q-any-j.md; its appended q=8,j=5 section covers the only remaining signature. |

The original size-21 input, monotone graph properties and gate conventions are those of the listed dependencies. PAYLOAD.sha256 covers every text in this packet other than the manifest itself. This is a mathematical research deposit, with no new solver run or Lean certificate.
