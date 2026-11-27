# Fourteen-input threshold two at 34 gates and eight ANDs

The signed manuscript degree/fourteen-final/eight-and.md excludes this composition for every number of incidence flags. Its SHA-256 is 14116b3c738f0e1d056742ead00b813c0f9315dea6bfa2c2b30b95123b4f2c15. It leaves other AND counts open.

## Reading order and prerequisites

1. The established size floors used here are C(10)=24, C(11)=27, C(12)=29, C(13)=32 and C(14)≥34. Reductions' threshold-dependency-map under reductions/ identifies the historical small-input source and certificate receipts. The unrestricted ten-input composition source is duality/uniform/ten-unrestricted-seven-and.md; the corrected eleven-input composition source is duality/uniform/eleven-unrestricted-eight-and.md. The latter uses the corrected five-vertex path argument as recorded in the dependency map. The signed twelve-input exclusion is duality/uniform/twelve-unrestricted-eight-and.md; alternatively the main manuscript obtains it by regularization and deletion into the eleven-input exclusion.
2. Apply the raw-reader and clean-terminal normalization using the two-gate one-input-deletion gap, degree/t13-31/ten-tight.md and degree/t16-cyclic-build/ten-forest.md. Flattening gives the relative budget v−2. Use the five-or-higher degree exclusion **before** invoking the earliest-AND existence argument. The independent high-degree source geometry/fourteen34/eight-and-high-degree.md supplies this bound. Equivalently use the star restriction, full-order nonstar remote transfer in duality/uniform/fourteen-cycle-component-transfer.md and the independent raw increment in comb/fourteen-construct/independent-raw-or-increment.md.
3. With maximum degree at most four, use the first paragraph of degree/t14-34/eleven-branch-roles.md to obtain a branching pure group. Its OR frontier loses two ORs; use the frontier factor argument of degree/t14-34/eight-five-511.md. Removing its pendant neighbors also loses distinct raw injections. The retained graph has N−3 decoder ORs after branch deletion. Degrees two and three are ruled out by the twelve- and eleven-input composition exclusions.
4. For degree four, the full-order remote transfer forces a star forest. The two-three-star bound in degree/t16-pair-stars/two-three-stars.md applies to the residual forest. The short-path collector count and quartic leaf-injection chronology are in the signed main manuscript. They contradict the four-OR floor for threshold two on four inputs.

## Verification scope

Source and dependency review covers the normalized physical circuit and the transfer to arbitrary representatives. The source receipt does not constitute a Lean verification or a new run of archived search certificates. Use sha256sum -c SHA256-MANIFEST in this folder to verify the frozen files.
