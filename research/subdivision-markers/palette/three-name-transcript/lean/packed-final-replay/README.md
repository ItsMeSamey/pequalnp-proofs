# Independent packed refinement replay

The six core modules were rebuilt from source at commit 73c18aff095ccfe11bb60bfd3c7097fca033fbb5. Four generated modules were rebuilt from commit 1e5069a42584dc63c806a9e1829ace79d809db25. Each immutable snapshot is the subtree research/subdivision-markers/palette/three-name-transcript/lean. For exact object identity the clean runner compiles via the canonical absolute source filename, checking its bytes against the frozen snapshot before and after. Project dependencies are rehashed and linked individually into an isolated prior directory. Only the nine verified host objects, one verified Gaussian object and the six freshly built core objects are reused.

To reproduce, create a fresh tmpfs work root with empty core, fixture, prior and fresh directories, recording its path in workdir. Extract each Git subtree there in its corresponding source directory. On the exclusive serial compiler slot run core.sh and then:

    python replay.py fixture 1e5069a42584dc63c806a9e1829ace79d809db25 PACKED-FIXTURE-SOURCES.sha256 c7b135c01638e29d4509efb014aae1c4f7f45f13087ea5bf6de9072ac5a01bae packed-fixture-producer 5ebb757e61a773f1620fcf82d31f6b35371fcab29395bb822570087df0f1e315
    python verify-input.py

The first two runners compare all new compiled objects and complete logs against the immutable producer, while monitoring the compiler guard. A canonical import-only axiom probe follows each stage. The input verifier regenerates the four sources directly from published JSON/generator/templates, compares source hashes and reruns the independent physical enumerator. See scope.md for the precise distinction between generic typed correctness, the closed original-index negative fixture, and the JSON input.
