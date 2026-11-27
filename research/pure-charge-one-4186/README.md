# Vertex-cover bound for one pure exceptional OR gate

The Lean theorem `PEqualNP.Outside.L_meta_4186_aux.Q1Pure.complete` proves the cover bound for a nonempty four-cycle-free graph and a least top-form AND/OR circuit computing its edge function. It assumes that exactly one OR gate belongs to `orN ∖ lam` and that every gate strictly inside its cone is an OR gate.

The theorem gives a vertex cover whose cardinality plus the number of residual edges is at most the number of noncentreless tops plus twice the number of centreless tops plus the number of junk ANDs. See [the theorem](src/Q1PureComplete.lean) and [the replay instructions](BUILD.md).

The package contains every local module required by the proof and its axiom probe. [Source hashes](sources.sha256) identify the bundled Lean files. The [upstream manifest](upstream.sha256) and [provenance record](provenance.json) identify the pinned project definitions, toolchain and package dependencies.
