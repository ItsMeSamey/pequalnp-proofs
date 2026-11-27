# A residual-cover counterexample for 18802

The single-file Lean theorem `PEqualNP.Research.L_meta_18802_refuted` proves the negation of the issued proposition. The circuit is a 13-gate least AO2 circuit for two disjoint bull graphs. Its six residual edges require four cover vertices, while the issued bound allows only two.

Compile `Neg18802Flat.lean` against the pinned project’s `PEqualNP.Defs`, then compile `Neg18802FlatAxioms.lean` with that object on the Lean path. The source manifest stores the exact issued-proposition hash, all direct source dependencies, the three axiom reports, and the source provenance for the six-input lower bound. The kernel manifest separates captured central receipts from prebuilt upstream helpers. The flattened proof imports only `PEqualNP.Defs` and contains the helper proofs in its own namespace.
