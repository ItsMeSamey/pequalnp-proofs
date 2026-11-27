# Eight-input edge existence: circuits of size at most thirteen

The [integrated manuscript](site-team-01/32081/size13-all-index.md) gives a source-level proof for the size-at-most-thirteen branch of L-meta-32081. Its [singleton cases](site-team-01/32081/size13-singleton-index.md) and [physical descent](site-team-01/32081/descent13.md) are separate indexed dependencies. The [size-fourteen status](site-team-01/32081/size14-all-index.md) identifies open strata. This packet is neither a complete proof of the unbounded issued theorem nor a compiled Lean certificate.

The [issued theorem](lean/PEqualNP/Outside/L_meta_32081.lean) and its [gate evaluator](lean/PEqualNP/Defs/CircuitLowerBounds.lean) are reproduced as original source. The independent Python census parses the graph directly from the pinned issued text and requires only Python 3.10 or later. It counts partitions satisfying necessary conditions, including 1,528 full-graph partitions with six classes. The manuscript supplies the separate structural arguments. The [original run receipt](site-team-07/32081-class-replay/receipt-13h318ni/receipt.json) and its frozen input copies are included.

Unzip into an empty directory, then run:

    python3 verify.py
    python3 verify.py --census

The first command checks the SHA-256 manifest. The second independently regenerates both ordered-class counts and checks the complete result against the frozen receipt. The archive preserves relative source links. Supplementary files quoted by the manuscript are source evidence; partial Lean developments depend on the external Lean/Mathlib environment and are not required to verify or replay the census. [Independent review record](REVIEWS.md).
