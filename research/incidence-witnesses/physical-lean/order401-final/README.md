# Order-401 incidence circuit bound

Lean 4.36.0 verifies `IncidencePhysical401Caller.scalar : IncidenceOfficialScalar.ScalarLower401`. Under its order-401 incidence, circuit and sparse-test hypotheses, the circuit has at least 646425 gates. The entry module is `IncidencePhysicalPosted401`. The terminal declaration `IncidenceOfficialScalar.physical_posted401` has the exact posted binder order specialized to 401. Its recorded axiom report lists `propext`, `Classical.choice` and `Quot.sound`.

## Contents

The dependency-ordered manifest lists 255 local source modules, their SHA-256 digests, source locations and the Lean objects selected by the successful producer. Every research source required by the entry module is in `src/`. Original path names identify provenance. Available producer logs, memory traces and final import-resolution records are under `receipts/`. The toolchain and package lock identify the external Lean and mathlib libraries.

## Replay

Run these commands from the extracted directory. The first checks all archived files against the inventory. The build uses a new output directory, runs Lean once per module and saves fresh logs. It requires Python 3.11 or later, the pinned Lean toolchain and mathlib libraries.

```sh
python3 replay.py verify
lake exe cache get
lake env python3 replay.py build --output ../q401-rebuilt
```

A pinned project with the same external packages can supply its Lake environment for the build. The replay process excludes that project's own build objects and checks the external library hashes before compiling. Use `--count 3` to restrict a run to the next three unbuilt modules. The final object and terminal axiom log are written under the specified output directory.

See `src/IncidencePhysicalScalar401.lean` for the last scalar proof step and `src/IncidenceOfficial401.lean` for its exact hypotheses. The source and object selected by the producer are separately recorded, since rebuilding from another root can change object bytes.
