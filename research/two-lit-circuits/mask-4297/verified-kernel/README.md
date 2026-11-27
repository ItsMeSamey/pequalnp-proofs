# Seven gates are necessary and sufficient for L-meta-23724

L_meta_23724.lean proves the negation of the stated six-gate existence proposition. The theorem quantifies over every fan-in-two circuit, all five inputs, and every ordered pair, including repeated indices. Control23724.lean checks the seven-gate upper construction.

The pinned Lean 4.36.0 physical proof uses the exact 15-row promise projections and the six-row numerical ledger (346 transitions). Physical modules, final theorem and axiom report compiled; historical generic helpers were reused from their checked 25057 objects. The package contains the complete source closure including those helpers and a standalone replay driver. The only external imports are PEqualNP.Defs and Std. Run python3 replay.py --audit-only for source and dependency checks. To rebuild all 20 modules from source supply --lean-project and an empty --build-dir to the same script.

The endpoint axiom report is receipts/Axioms23724.log: propext, Classical.choice, Quot.sound. The successful module receipts include guarded-noM-probe.log, the first line of physical-final.log for MaskCode23724, and link-final.log for all subsequent modules. Resource guard interruptions before this successful build are retained for provenance.
