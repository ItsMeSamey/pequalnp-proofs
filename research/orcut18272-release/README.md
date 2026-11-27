# Four productive OR gates are necessary for L-meta-18272

Every witness to the supplied statement requires at least four OR gates whose outputs enlarge the current intersection closure. In particular, the six-intermediate-gate, eight-terminal-pair branch is impossible. The larger gate-count branches remain open. This package supplies two reproducible finite enumerations and a mathematical reduction. The Lean source records the issued goal with its original placeholder.

## Instance

The file `instance/statement.lean` reproduces `lean/PEqualNP/Outside/L_meta_18272.lean` byte for byte as checked against the working copy. Its SHA-256 is `9ec4bd7fce25977e79676fd87f567c30812b34f80a264e9df1a9aeb6d972f84b`. The eleven decimal masks in `instance/raw-masks.json` are the input values in statement order. Both C++ sources embed these same masks. Bits 0–15 are positive rows, bits 16–39 are negative rows. Each internal gate must hit both bands. The bitwise union of all terminal intersections must equal 65535.

## Reduction

1. Write n for the number of internal gates and t for the number of listed terminal pairs. The constraints n ≥ 6 and n + 2t = 22 imply t ≤ 8. At n = 6, t = 8 and at least three of the six gates must be AND gates, leaving at most three physical OR gates.
2. Start with all nonempty intersections of the raw masks. Throughout the search, give the computation every nonempty intersection of the raw masks and the OR outputs admitted so far. AND gates are then free. Any physical AND value belongs to the bank by induction. If a physical OR has operands in the bank and its output is already in the bank, skip it. Otherwise add its output and close under intersection. Call the latter OR productive. Every physical gate is mixed, and all raw masks are mixed, so both operands of a productive OR must be mixed. Equal operands cannot enlarge the bank. This induction preserves the chronological order of the remaining gates. It relaxes the limits on internal ANDs, their mixedness and wire use.
3. Every terminal pair in the original computation yields an intersection in the final bank. Each nonempty contributing terminal has only low bits, since any negative bit would survive the output union. Permit every such bank value as a terminal at no construction cost. Duplicated terminals can be removed. The relaxed acceptance question is whether at most eight terminals cover all sixteen low bits.
4. Every two distinct raw masks have a nonmixed intersection with at most one low bit, and each low singleton is realized by a clean raw pair. The supplied check verifies both facts. Any intersection containing two distinct raw masks therefore cannot serve as a mixed OR operand or a multirow clean terminal. The producer can restrict candidate intersections to a subset of previous OR outputs with at most one raw mask. It omits the empty intersection as a wire; singleton terminals are always available.
5. Both enumerations reject the initial bank and find zero covers at depths one, two and three. The unpruned chronological search independently suffices for completeness. Therefore every issued witness needs at least four productive ORs. This contradicts the bound of three physical ORs at n = 6.

## Enumeration receipts

| Productive ORs | Canonical producer paths | Chronological independent paths | Successful covers in either search |
|---:|---:|---:|---:|
| 0 | 1 | 1 | 0 |
| 1 | 55 | 55 | 0 |
| 2 | 4,555 | 6,040 | 0 |
| 3 | 532,653 | 1,140,785 | 0 |

The 55 first-OR outputs define the shard indices in increasing numeric order. Each program merges equal output masks at a fixed prefix. The independent search keeps every subsequent chronological ordering. The producer suppresses a smaller OR output if it had already been available before a larger chosen output. For any successful list of target outputs one may choose the least currently available target output first, skip targets already in the enlarged closure, and continue. Enlarging the bank preserves the availability or redundancy of the other target outputs. This gives a canonical path within the depth bound. Different dependencies and redundancies yield different numbers of chronological representatives, so there is no fixed conversion factor between the two path counts.

The producer drops dominated terminal masks and branches on an uncovered low bit; an individual singleton is an explicit fallback. If the union of multirow masks contains at most eight rows, covering all sixteen needs at least nine taps (or sixteen if there are no multirow masks). The independent implementation keeps the full intersection closure, including zero and high-only masks. It enumerates subsets of multirow clean terminals and completes the remainder with singletons. Its startup test compares its cover decisions against direct union enumeration on 128 four-row families at five budgets, giving 640 control decisions. Further details and the original independent method description appear in `independent/METHOD.md`.

## Reproduction

From the extracted package directory, run `./run.sh verify` to check SHA-256 file integrity, input consistency, raw-pair properties, all shard indices and the recorded totals. Run `./run.sh full` to compile both C++20 programs in temporary storage and compare freshly computed output against every shard receipt. The modes `controls`, `producer` and `independent` select individual replays. Requirements are Bash, GNU sha256sum, Python 3.10 or later, sed, diff and a C++20 compiler for native replays. Set CXX to select a compiler. The producer log includes historical launch and timing lines; replay compares the deterministic shard lines. Independent receipt columns are shard index, first OR mask, and visited/hit counts at each of depths 1, 2 and 3.

This conclusion applies to the issued eleven masks, mixed intermediate signals, and a budget of eight terminal pairs. It neither supplies a target witness nor certifies impossibility for circuits with four or more productive ORs. Neither C++ enumeration is a Lean kernel proof.
