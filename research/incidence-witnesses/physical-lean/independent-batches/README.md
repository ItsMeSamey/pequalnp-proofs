# Serial incremental replay

Create an empty tmpfs work root, record its path in workdir, and create directories ten, marks, round, hoist, fresh and prior. Into the first three extract the research/incidence-witnesses/physical-lean subtrees of the respective commits named in replay.py. Into hoist extract the hoist subdirectory of its release's physical-lean subtree. Use the sealed q401 baseline and increments as specified in the driver's three prior receipt hashes.

Run python replay.py 3 per reserved three-source checkpoint. The ledger is persistent: on each invocation all prior dependency objects, every frozen source manifest and all objects accepted at earlier checkpoints are rehashed. Each committed ledger entry identifies the source, resulting object, complete log and direct imports resolved. Dependencies are built in topological order and each source is compiled once. The additional native Research dependencies are extracted from immutable repository source and their fresh objects compared against the earlier native research-library build. Hoist producer diagnostics serialize canonical input paths, so those source bytes are verified against the frozen snapshot before invoking the compiler via that path.

Once an increment has all its objects, its stage receipt records an import-only axiom probe for each of its public named theorems. The final receipt binds all four receipts to the complete ledger. The script uses a fresh -j1 compiler under a private-memory/time guard.

For the later ten hoist sources create fullhoist with the hoist subtree of 8808fdae5012178edbd92c5485d4dac82eb7894b. Its complete manifest contains 19 modules. The driver checks that the nine overlaps have equal source and target object hashes and adds exactly ten new tasks.
