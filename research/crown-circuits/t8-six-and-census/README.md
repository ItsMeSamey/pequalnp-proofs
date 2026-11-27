# Singleton behavior of all 19-gate threshold-two circuits on eight inputs with six ANDs

Every AND in such a circuit rejects every singleton. The circuit is binary, monotone, allows arbitrary fanout, and computes threshold two on the full Boolean cube. The known eight-input optimum is 19 gates. The statement describes optimal circuits of this composition; all-clean examples exist.

At least one AND rejects every singleton, by following the output backwards through its final ORs. Thus an exception would have one, two, three, four or five singleton-hot ANDs. The five exhaustive results below reject each case. The one-pin deletion and re-splitting argument admits raw inputs with literal signed masks; the solver handles the resulting nonliteral masks. The all-clean extremal-cover theorem then gives a complete partition of the six-axis sign cube by the raw signed masks.

| Hot count | Canonical cases | Evidence |
|---:|---:|---|
|1|5 widths|t8-one-dirty.md and one-dirty-width*.log|
|2|156 profiles|t8-two-dirty.md and t8-two-exact-ledger.tsv|
|3|4,212 protected profiles|three-template-method.md and t8-three-exact-ledger.tsv|
|4|28,140 orbit representatives|t8-four-dirty.md and t8-4-profile-ledger.tsv.gz|
|5|116,820 orbit representatives|t8-five-dirty.md and t8-5-profile-ledger.tsv.gz|

The eleven relabeled three-hot cases are checked by an explicit signed-axis canonicalization. The two high-count ledger orbit sizes expand to 83,927 and 510,294 chronological profiles respectively. Independent review matched every high-count ledger row against the historical execution receipts, including all root subdivisions. The packaged replay recomputes the five-hot case without root subdivision; it compares each final pair of totals with the frozen ledger.

For regular ten-input 24-gate, six-AND circuits, a branching pure doubleton would restrict to exactly this eight-input profile while preserving all six axes and the old signed masks. Complete signed coverage prohibits the two outside labels. See ten-branching-doubleton.md, signed-cover-extension.md and ../uniform/single-level-extremal-cover.md. The unrestricted existence of a ten-input circuit at this composition remains open.

## Checking the package

From the extracted archive root, run the following in a POSIX shell with Python 3 and a C++20 compiler. Verification of traversal counters used GNU C++ 14.2.0 and its standard library.

    sha256sum -c T8-MANIFEST.sha256
    cd duality/ten-six-lift
    python3 replay-t8.py
    python3 high-control.py
    python3 three-control.py
    python3 semantic-control.py

The default replay command checks the archived ledgers, catalog totals and the eleven signed permutations. It takes less than a second on the original machine. For an independent reconstruction of the full search, run each stratum separately.

    for d in 1 2 3 4 5; do python3 replay-t8.py --replay "$d" || exit 1; done

Each run compiles the corresponding original C++ source and creates fresh input and output in a temporary directory. Strata two and three also rerun the Python catalog generators; strata four and five reconstruct the entire protected-mask catalog and topological orbit partition from C++ sources. Every direct search must return zero hits and the recorded count of bank nodes and semantic fronts. No network, Lean installation, Git repository, tmpfs work paths, prebuilt binaries, or historic run logs are needed for this reconstruction. The two largest strata involve sustained CPU computation. The shipped one-through-five ledgers are from the reviewed runs; the all-in-one full replay was not repeated for this archive.
