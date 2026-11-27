# Vertex-cover bound for one exceptional OR gate with two dirty AND inputs

The Lean theorem `PEqualNP.Outside.L_meta_4186_aux.Q1Double.complete` proves the issued cover inequality for a four-cycle-free graph with at least one edge and a size-minimal fan-in-two AND/OR circuit computing its edge function. The circuit must satisfy `TopForm`. Exactly one OR gate belongs to `orN ∖ lam` and its two inputs are outputs of gates in `junk`. The exact hypotheses and conclusion are in [DoubleDirtyCase](src/Q1DoubleEndpoint.lean).

Writing `S` for the vertex cover, the theorem gives

```text
|S| + |Ustar| ≤ |tops ∖ centreless| + 2 |centreless| + |junk| + 1.
```

The proof classifies how the two AND-input regions share gates with other centreless tops. The four cases are private arms, one external top on a single arm, several external tops on a single arm, and one external top shared by both arms. Each case charges the cover to gates in the original circuit. The [case assembly](src/Q1DoubleRealizedComplete.lean) and [final theorem](src/Q1DoubleComplete.lean) connect these bounds to the issued statement.

The kernel accepted the final source SHA-256 `e66dc55253c25e402a766fcbece853f1f2b22bc04fa0024ea3b9949484075fd8`. Its compiled object SHA-256 was `b085acc79b0903726eb7ce37807f7359bda018eb32aa9cfc6369ebf765d7881b`. The [axiom probe](src/Q1DoubleCompleteAxioms.lean) reported `propext`, `Classical.choice` and `Quot.sound`.

The package contains the 179 proof modules and the axiom probe. [Source hashes](sources.sha256), [upstream inputs](upstream.sha256), [toolchain and package pins](provenance.json), and [build instructions](BUILD.md) support an independent replay.

The [kernel manifest](kernel-manifest.json) records the source and object hashes for each bundled module and its direct imports. Its evidence labels distinguish contemporaneous compiler receipts, historical direct-import hashes reconstructed from unchanged objects, and isolated compilations that reproduced the original objects byte for byte. Run `python3 verify_bindings.py` to check these relationships against the shipped source.
