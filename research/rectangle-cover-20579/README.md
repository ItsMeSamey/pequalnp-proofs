# Positive rectangle covers for L-meta-20579

The minimum number of all-one rectangles covering the labeled 32 × 32 graph in L-meta-20579 is **between 28 and 30 inclusive**. Integer weights on the 411 edges prove the lower bound. A list of 30 rectangles attains the upper bound. Whether 28 or 29 suffice remains open here.

## Replay

Run the following command from this directory with Python 3.10 or later. The checker uses only the standard library.

```sh
python3 -I -B check.py
```

The 32 hexadecimal words in `graph.json` reproduce the row list in the public mathematical statement L-meta-20579. The source statement is included verbatim in `statement.txt` with a trailing newline. Its SHA-256 digest is `e233b9b26bab1a8856b41abefce91ad2660f5139effd3df1ad8e11582240f816`. Both indices start at zero. Cell (u,v) is an edge exactly when bit v of word u is one, with bit zero the least significant bit.

## Completeness of the rectangle dictionary

A positive rectangle is a product of nonempty row and column sets containing only edges. For a nonempty row set S, let B be its common neighborhood. If B is nonempty, let A consist of every row containing B. As S is contained in A, the common neighborhood of A equals B. The rectangle A × B is maximal because every compatible row and column is already present. Conversely, for any maximal rectangle, the common neighborhood of its rows equals its column set, and its rows include every row containing those columns. This construction therefore enumerates all maximal rectangles.

Starting with the full column mask, keep each previously seen mask and intersect it with the next row mask. Induction on the prefix of processed rows gives exactly the intersections of all subsets of that prefix, including the empty subset. After processing all rows, discard the empty column mask and masks with no supporting row. Pair the remaining masks with all their supporting rows. This yields 1,893 distinct maximal positive rectangles.

## Integer certificates

The 411 entries in `rectangle_dual.json` assign nonnegative integer weights to the edges in row-major order, skipping zero cells. The checker computes each maximal rectangle's weight by summation and finds a maximum of D = 999,998. Every positive rectangle lies inside a maximal one since the graph is finite. Nonnegativity bounds its weight by D as well.

Any cover by h positive rectangles counts every edge weight at least once, even when rectangles overlap. Thus hD is at least the total edge weight W = 27,118,284. Since W − 27D = 118,338 > 0, every cover needs at least 28 rectangles. The certificate binds the regenerated dictionary by SHA-256 of the lexicographically sorted rectangle pairs encoded as compact JSON decimal arrays followed by a newline.

Each pair in `cover30.json` specifies unsigned row and column masks. The checker takes the union of all 30 rectangles and compares it with the target across all 1,024 cells.

This bound counts positive rectangles. Constructing their selectors costs gates, and a circuit can share intermediate signals and use negation. The existence of a fan-in-two circuit with at most 170 gates for this graph remains a separate question. The finite cover result leaves P versus NP open.
