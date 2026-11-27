# Replay from a clean checkout

Use Python 3.9 or newer, Git and Elan. From this package directory, clone the pinned upstream project and select the recorded revision. A clean setup needs network access for the toolchain and Lake dependencies.

```sh
git clone https://github.com/ItsMeSamey/pequalnp-proofs.git upstream
git -C upstream checkout --detach b104ff3988c176aae2db960c2a71ddf975ef047c
python3 build.py upstream --plan
```

The plan verifies both manifests and prints the import order for the 180 bundled modules. The Lean toolchain is 4.36.0. The upstream Lake manifest pins Mathlib and the other packages. To shorten the initial dependency build, download the upstream Mathlib cache, then run the local proof replay.

```sh
(cd upstream/lean && lake exe cache get)
python3 build.py upstream --output checked-objects
```

The output directory must be new. Omit `--output` to discard the objects after a successful check. The script builds the upstream definition module and the direct Mathlib dependency, obtains Lake's package paths, and checks the bundled modules sequentially. The bridge source is included in `src/`. Its object and the Q0 and Q1 objects are produced in this run.

The final probe reports the axioms of `PEqualNP.Outside.L_meta_4186_aux.Q1Double.complete`. The script requires exactly `propext`, `Classical.choice`, and `Quot.sound`. Source hashes identify the proof. Compiled object hashes can vary across build environments.

With `--output`, the output directory also contains `kernel-bindings.jsonl`. Each row records a successful Lean command with its source hash, the object hash of every direct import, the source hash of each bundled direct import, and the emitted object hash. The runner checks the input hashes before and after each compilation.
