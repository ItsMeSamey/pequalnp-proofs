# Fixed-prefix lower bounds for L-meta-18968

The supplied raw theorem declares 34 successive AND/OR gates. At each slot the original permitted source wires are 0 through 43, wire 54, and any earlier slot. The verifier reconstructs the two packed inputs by rotating 13-bit lanes and checks the target labels directly at the 676 bit positions. It pins the exact formal statement by SHA-256.

The certificate seed numbering lists raw wires 0–12 then 19–43 as its first 38 signals. Each fixed prefix gate appends its output in order, starting at index 38 (raw wire 55). Only the first 21 gates of seed 18968 and first 18 gates of seed 21968 are fixed. The remaining seed recipes are metadata. All original permissible sources, including wires 13–18 and 54, are available during completion.

For a positive and a negative sample, take the set of signals that are 1 on the positive and 0 on the negative among all original sources and fixed prefix outputs. A monotone output cone separating the samples must depend on at least one such signal. Otherwise every cone input is at most as large on the positive as on the negative. Pairwise disjoint difference sets therefore require distinct cone inputs. A connected output cone with g binary gates has at most g+1 distinct input signals, since it has at most 2g incoming edges and at least g+t−1 edges to connect its g gates and t distinct input signals. Treat prefix outputs as available inputs even when a completion reuses them multiple times.

Each certificate encodes pairs as 38-bit projections. The checker finds corresponding raw positive and negative bit positions. It then adds raw bit positions 0 (positive) and 52 (negative), whose projected positive is dominated by the projected negative. The checker tests all difference sets directly with the seven additional original sources restored. Seed 18968 gives 15 disjoint sets and requires at least 14 new gates, with 13 available. Seed 21968 gives 18 and requires at least 17, with 16 available. Both fixed-prefix families are excluded even when the completion may freely use wire 54. The unrestricted theorem remains open.

Run from this directory with Python 3 using only the standard library.

```sh
python verify_packing.py L-meta-18968.json packing-18968.json packing-21968.json
```

## Downward-closed gate sets

The two subset certificates each select 15 named seed slots. Their inputs all come from original wires or earlier selected slots. Supply both subset files as additional verifier arguments. Each yields 21 disjoint sets after adding raw pair (0,52). At least 20 further gates are required, with 19 available. This applies to any 34-gate architecture containing those 15 distinct gates with that wiring, even if other gates are interleaved or the selected subprogram is renumbered.

On the normalized residual the [mixed-gate complexity](mixed.md) is exactly 13 when arbitrary monotone functions of either side are free.

A [complete suffix search](suffix-search/COPY.md) excludes freezing the first 15 gates of either seed in the normalized 33-gate residual problem. It allows arbitrary binary monotone suffixes with shared intermediate wires.

[Raw-to-residual transfer](raw-transfer.md) proves that the optimal raw suffix uses exactly one more gate than the optimal normalized residual.

[Point-boundary accounting](charge-review.md) proves that every residual solution using at most 33 gates requires at least eight distinct point-side boundary signals and at least 14 mixed gates, with no bound on line-side signals.

[An eighth point signal](../extra-point/README.md) still needs at least 20 point gates if the other seven point signatures are the canonical neighborhoods. Together with at least 14 mixed gates this excludes such an architecture at size 33.

[Eight point signatures](eight-signatures/fourteen.md) exclude 14 mixed gates at total size 33 by classifying all 202 noncanonical signatures. Any size-33 solution therefore requires at least 15 mixed gates.

[A single extra read](nine-boundary.md) excludes the remaining six eight-point families at 15 mixed gates. Any 33-gate separator therefore requires at least nine point-side boundary signals.

[Any read-once mixed tree](read_once_guards.md) with exactly seven line-side boundary inputs needs at least 34 residual gates, for any number of point-side inputs. With the nine-point boundary bound this excludes 15 mixed gates at total size 33.

[Six canonical signatures among nine](../six-of-nine/README.md) require at least 18 paid point gates when exactly six of the canonical neighborhoods occur. With the 16-mixed-gate minimum this excludes these nine-point architectures at total size 33.

[The nine-signal enumeration](nine-signatures/README.md) and [mixed-cone exclusions](sixteen-mixed/README.md) show that a residual solution of size at most 33 requires at least 17 mixed gates and ten point-boundary signals.

At equality the [21-gate point circuits](point-equality.md) consist of seven disjoint OR trees. An [OR of point-by-line products](rectangle-dag.md) needs exactly 34 residual gates, even with shared computation on each side. Run `python3 verify_star.py` in this directory to check both star orientations on the raw samples.

For ten point-boundary wires whose signatures extend one of the 202 noncanonical eight-mask bases, [the complete extension profile](../ten-supersets/README.md) forces 17 paid point gates and excludes 17 mixed gates at the 33-gate budget.
