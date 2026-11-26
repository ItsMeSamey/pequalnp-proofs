# Reproducing the eleven-input certificate

Run commands from this directory. The fast audit checks the exhaustive 2,048-assignment upper control and checks complete class IDs, expected partitions, and zero outcomes for the archived search data. It uses Python 3 and its standard library.

```sh
sha256sum -c SHA256SUMS
python3 -B audit.py
python3 receipts/audit-projection.py seven
```

Full finite regeneration uses a C++20 compiler. Supply new writable output directories; the output paths in these commands are examples. Low-dirty replay compares every repeated output with the archived rows. The two-dirty replay also regenerates the 27-gate positive control and checks an eleven-versus-ten receiver boundary. The higher-dirty replay generates physical chronological templates, tests the opposite-sign and matching cases, checks the fixed-anchor positive control, and insists on complete row reconciliation.

```sh
sh replay_low.sh /tmp/eleven-low
(cd seven && sh replay_two.sh /tmp/eleven-two)
for d in 3 4 5 6; do
    (cd seven && sh replay_higher.sh "$d" "/tmp/eleven-$d")
done
```

The generated per-dirty-count outputs are independent and can run simultaneously if CPU and disk allow. `audit.out` records the completed archival validation. The full two-dirty replay was repeated from a fresh build and matched every finite-search output byte for byte. The higher-dirty ledgers retain every required class ID and detector outcome; `receipts/audit-projection.log` records an independent computation of 4,720 signed-port projections. The six-AND provenance receipts were independently reconstructed; their primary reproduction instructions live in the published six-AND package. `receipts/audit_ledgers.py` expects that original working tree's hard-input tables and canonical forest corpus and is supplemental to the standalone six-AND replay.

Paths inside the original per-stratum notes may retain the working-tree spelling. In this package the physical template generators are `seven/templates11.cpp` and `seven/templates11_reference.cpp`; the shared-pin, matching, star and component arguments are in `lemmas/`. All runnable search code references only files in this package.

## Previously published dependencies

Commit IDs below refer to the ItsMeSamey research fork. Each path is relative to the root of that repository.

| Use | Immutable revision and path |
|---|---|
| Eleven inputs, at most six ANDs at size 26 | `694c7e038d4e7d7201f88f84bfe2f719dd69c8b9`, `research/crown-circuits/eleven-six-26-cert/PROOF.md` |
| Exact unrestricted ten-input minimum of 24; direct-minor and singleton clean-up arguments | `8954e3c63e98f288bcaa14d9d6aae477165a834e`, `research/crown-circuits/ten-exact-cert/PROOF.md` and its `dependencies/` |
| Eleven-input unconditional 26-gate floor | `769947641e531fd0c3915263a7c58a734e9a224d`, `research/crown-circuits/threshold-twelve-final-cert/eleven-proof.md`, combining the seven-AND obstruction with the at-most-six-AND floor in `05d498a339429f855b7afa64d8e3ad3822444bc8`, `research/crown-circuits/threshold-eleven/ELEVEN.md` |
| Eight- and nine-input lower bounds used in the eight-AND argument | `2111f5f62b25a858972abddd75ee7d8f134eebd2`, `research/crown-circuits/threshold-eight/` and `research/crown-circuits/threshold-nine/` |
| Physical OR-floor theorem and normal-form, star and component arguments | `769947641e531fd0c3915263a7c58a734e9a224d`, `lean/Research/WegenerThreshold.lean` and `research/crown-circuits/threshold-twelve-final-cert/` |

The formal Lean file proves the general OR-floor ingredient. The unrestricted 27-gate conclusion combines mathematical reductions and finite C++/Python search evidence.
