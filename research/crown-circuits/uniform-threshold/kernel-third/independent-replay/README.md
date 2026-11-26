# Independent clean replay of the signed threshold-two power bound

The target is `ThresholdRegularThird.bound_power`. Write z = size − 2n − √(2n). For n≥2^402, every fan-in-at-most-two monotone circuit computing threshold two on the full Boolean cube satisfies z≥0 and n³≤(2¹⁵z)¹⁰. The second public declaration checked is `ThresholdRegularThird.regular`. The real-exponent convenience wrapper lies outside this source manifest.

The verifier extracts the source package directly from the Git commit in `source-lock.json`, checks the manifest digest, verifies all 187 source digests and topological order, and compiles serially with Lean 4.36.0. All six PEqualNP project modules are compiled along with the remaining 181 modules. No previous threshold build or public-project object directory is on the search path. For every invocation, `lean --deps` records its actual imports. Every manifest-local dependency must resolve to previously rebuilt output in this run. The external package revisions must agree with the pinned Lake manifest.

`receipt.json` seals the environment, object hash table and resolved import table. `kernel.log` contains the compiler diagnostics; `axioms.log` records both public declarations. `independent-check.txt` records a second pass over sources, objects and import edges.

On the pinned host, copy the scripts and source lock into a separate empty receipt directory, obtain the Lean compiler slot, and execute `bash prepare.sh`, `python replay.py`, then `python verify_receipt.py`.
