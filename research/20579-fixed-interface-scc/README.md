# Shard 53 restricted circuit certificates for L-meta-20579

**Theorem.** Neither of the following two finite circuit families contains an exact circuit for the 32-by-32 target relation with at most 170 physical gates. Family definitions are bound to the input recipe archive and the ordered physical prefix gates in each model's `meta.json`.

- **Narrow family.** Charge all 84 listed prefix gates. The suffix may select up to 86 distinct nonprefix functions from the narrow selector table, with one selected AND, OR or NOT recipe per active result and shared fanout. The extra prefix recipe combines physical wires 25 and 89 by OR and costs one gate when selected.
- **Wide family.** Charge all 31 listed prefix gates. The suffix may select up to 139 distinct nonprefix functions from the wide selector table under the same accounting convention. Its extra prefix recipe combines wires 25 and 36 by OR and costs one gate when selected.

Each family permits acyclic physical dependency graphs rooted at the full target. The 64 raw inputs are row and column indicators. Truth-table bit `32*u+v` corresponds to the ordered input pair `(u,v)`. Both fixed prefixes place the first qualifying internal NOT at physical wire 69. Its output on the first six diagonal pairs is mask 0x35. The certificates establish a lower bound of 171 gates within these two enumerated families. Circuits using other physical prefixes or signal recipes are outside the theorem.

## Why the wide proof covers its whole family

The narrow unpinned CNF is UNSAT. The wide unpinned CNF additionally requires a change: either select the new wide prefix signal, or omit at least one of the 53 original providers that became selectable when the fixed prefix shrank from 84 to 31. That CNF is also UNSAT. If the change condition is false, those 53 original providers are all selected and the new prefix is absent. Prepaying the 53 distinct providers restores the narrow prefix. The remaining goal-reachable recipes belong to the narrow selector table; at most 139 minus 53, or 86, suffix gates remain. Team 07's wide audit checks this contraction against the supplied recipe tables. Together the two certificates cover both truth values of the change condition.

## Reproduce

Run `python verify.py` in the extracted package with Python's assertions enabled and `python-sat==1.9.dev25` installed. The replay checks every listed file hash, reconstructs and compares both CNF clause multisets, checks the physical prefix and target, checks the guard contraction, then validates both DRAT proofs. It uses the archived Linux x86-64 checker. On another platform run `python verify.py --compile-checker` with a C compiler, or supply `--checker /path/to/drat-trim`. Use `--audit-only` to run just the encoding and byte checks. The archived checker source includes its license.

The original team 07 audit and checker sources and logs are preserved byte-for-byte in `team07/`. The portable replay changes only the literal workspace paths at load time. `producer/` records source provenance and the narrow run's original verifier timeout. Team 07 subsequently verified the same narrow proof bytes. `narrow/` and `wide/` hold the exact DIMACS and DRAT artifacts, their physical encoding metadata, and final checkpoints.
