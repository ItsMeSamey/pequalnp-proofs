# One hidden AND in an original graph-9822 candidate

Suppose a fan-in-two circuit of size at most 17 computes the specified ten-input edge function on all 1,024 assignments. Its gates have the required unary or binary arity, and each operand refers to an input or an earlier gate. Repeated operands are permitted. If this same circuit has zero NOT gates, exactly six AND gates and exactly one physical hidden AND, it requires at least twelve OR gates. Six ANDs and twelve ORs exceed the size budget. [Original theorem](H1OriginalJoinedFloor9822.lean)

The hidden count is computed on the original circuit by taking its AND addresses and removing the frontier discovered from its output. The theorem uses the original gate counts throughout. A second declaration gives the contradiction directly for a reduced candidate. [Frontier definition](H1OriginalFrontier9822.lean) · [Reduced-sector corollary](H1ReducedSector9822.lean)

The proof splits on whether the hidden gate accepts a required negative row. The finite dispatch covers all 598 original cases, including 98 nonempty survivor lists across 64 pages. The independent audit matched 1,505 project modules and 14 external imports. The terminal axiom prints report propext, Classical.choice and Quot.sound. Other hidden counts and the signed six-AND case remain separate.

## Verification

Run `python verify_sources.py` to compare every project source with its recorded SHA-256 and display the three terminal compiler logs. The [complete project sources](project-sources.zip) extract into one module root for rebuilding in dependency order. Rebuilding requires Lean 4.36.0 and the external Mathlib, Std and PEqualNP modules pinned in the [manifest](h1joined-manifest.json). It records the imports, historical object digests and build evidence. The [independent receipt archive](h1joined-receipts-1459d7750cafcd4e.zip) contains the source-binding audit and terminal inputs.
