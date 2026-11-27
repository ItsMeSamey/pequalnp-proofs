# Original circuit capacity

This package contains the Lean proof of `SignedTrace.original_circuit_capacity` in `OriginalCircuitCapacity.lean`, all local modules it imports, and the upstream circuit definitions. For a finite AND/OR/NOT gate list with at most two listed operands per gate, the theorem bounds the number of live raw inputs plus distinct occupied first forks by the binary incidence charge plus one. It also bounds the number of distinct exceptional first forks by the number of output-live inverters minus one, using natural-number subtraction.

## Verify the package

After extraction, enter the `capacity-release` directory and run

```sh
sha256sum -c SHA256SUMS
./replay-fixtures
```

The fixture replay uses Python 3 and its standard library. It checks the truth tables and ordered signed pin paths of eight circuits. These examples exercise the path semantics used by the proof. The theorem itself is checked with Lean.

## Rebuild the proof and repeat the axiom audit

Install Elan and Lake, then run the commands below from this directory. On a clean machine, Lake needs network access for the pinned dependencies and their sources. The cache command downloads compiled Mathlib artifacts and can be skipped when building dependencies locally.

```sh
lake exe cache get
lake build CapacityRelease
lake env lean OriginalCircuitCapacityAxioms.lean > axioms.actual
diff -u audit/axioms.expected axioms.actual
```

The captured final audit lists `propext`, `Classical.choice`, and `Quot.sound`. The Lean toolchain is `leanprover/lean4:v4.36.0`. Mathlib is pinned to `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`; the complete transitive Lake package revisions are recorded in `lake-manifest.json`.

## Sources and licensing

The upstream file `PEqualNP/Defs/CircuitLowerBounds.lean` comes from `lean/PEqualNP/Defs/CircuitLowerBounds.lean` in the open-goat/pequalnp-proofs checkout at revision `b104ff3988c176aae2db960c2a71ddf975ef047c`. The upstream Apache 2.0 license is included in `licenses/PEqualNP-Apache-2.0.txt`. [Upstream source](https://github.com/open-goat/pequalnp-proofs/blob/b104ff3988c176aae2db960c2a71ddf975ef047c/lean/PEqualNP/Defs/CircuitLowerBounds.lean)

The top-level proof modules were assembled from the site-team-08 and site-team-09 workspaces. The fixture data comes from site-team-09 and the independent replay from site-team-07/r09. No separate license grant was supplied for these project-specific materials. Lake fetches Mathlib and its dependencies under their respective upstream licenses.
