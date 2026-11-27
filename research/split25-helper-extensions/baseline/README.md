# One two-coordinate feature on the split25 interface

For L-meta-20579, shard 53, fix the supplied 115-gate prefix and its 25 ordered output features. Allow one additional Boolean feature given by an arbitrary truth table on any two of the 25 coordinates. Grant both polarities of this helper for free. A flat signed DNF for the target still requires at least **82 tail gates**. A flat signed CNF requires at least **58 tail gates**. A 170-gate circuit with this fixed prefix has room for 55 tail gates.

The model uses binary AND and OR, with one final OR of conjunctions for DNF, or one final AND of disjunctions for CNF. Old literals are the 25 prefix ports and their individual negations. Each distinct negated old literal used requires one tail NOT gate. Inner expressions of the same operation can share subexpressions, and literals can fan out freely. The only additional available feature is the designated helper. A constant or unary helper is included by ignoring one or both of its inputs. This is a lower bound on these flat representations with this fixed interface.

## Replay

Run the following command with Python 3.10 or later from the package directory.

```sh
python3 -I -B check.py
```

The checker validates the bundled SHA-256 checksums. It reads the 32 row words from the public problem statement and reconstructs all 1,024 labels and 25-bit signatures directly from the prefix gates. Cell index `32*r+c` activates input wires `r` and `32+c`. Each port is one bit of the signature in the recorded order, starting at the least significant bit. The first NOT with an earlier internal operand must have output mask `0x35` on the first six diagonal cells. The checker validates all 1,225 positive-packing pair blockers, all 561 negative-packing pair blockers, and all 18 decreasing singleton edges.

## Packing after adding the helper

Consider two selected positive cells. Their supplied negative blocker agrees with them on every old feature on which they agree. A signed conjunction true at both positives is therefore true at that negative. The positive packing has 50 cells. Dually, the 34-cell negative packing has a positive blocker for every pair, so a valid clause can exclude at most one packed negative.

For a helper with arguments i and j, restrict a packing to cells where one of those coordinates is fixed to one value. Every old blocker of a retained pair shares the fixed value. On that fiber the helper is a unary Boolean function of the other coordinate. If that coordinate agrees across the pair, it also agrees with the blocker. If the coordinate differs but the helper agrees on both endpoints, the unary function is constant. In either case the blocker satisfies every augmented coordinate agreement. This proves that the pair certificates still apply to both polarities of every binary helper on that fiber.

For each of the 300 unordered input pairs, take the largest fiber obtained by fixing either input to either value. Group these fiber sizes by the number d of chosen coordinates among the 18 decreasing coordinates described below. The checker computes the minimum for each group.

| Number d | DNF packing | CNF packing |
| --- | ---: | ---: |
| 0 | 39 | 21 |
| 1 | 38 | 23 |
| 2 | 34 | 24 |

## Counting physical gates

A packing of size k requires k distinct terms or clauses, since each covers or excludes at most one selected cell. Each old feature assumes both values on both target classes, so no single old literal can serve as a valid term or clause. At most one of the two helper literals can be a productive unit term or clause. Thus at least k−1 distinct selected terms or clauses require a binary output gate. Combining k distinct outputs into one binary flat OR or AND requires at least k−1 additional gates. These final gates use the opposite operation from the nonunit term or clause outputs. Sharing internal partial conjunctions or partial disjunctions preserves the count of distinct outputs.

For each of 18 distinct old coordinates, the directional certificate supplies a target-one signature with bit zero and a target-zero signature differing only by raising that bit. Outside the two chosen helper inputs, each such pair has equal helper values. A flat expression using only the positive literal of this coordinate is monotone in it and cannot realize the required decrease. Therefore at least 18−d different old input negations must appear. Their unary gates are distinct from the binary gates already counted. Even after granting the helper and its complement for free, the resulting charge is at least 2k−2+18−d. Taking the minimum over the three groups gives 82 for DNF and 58 for CNF.

## Frozen inputs

- `public-task.json` is the public L-meta-20579 shard-53 task with its 32 hexadecimal row masks.
- `prefix115.json` is the original care25 prefix manifest with the source and physical wire numbers, gate list and cell records.
- `signed-cube-pack.json` is the original split25 positive packing and the source of the 18 directional witnesses in `negative_literal_edges`.
- `signed-clause-pack.json` is the original split25 negative packing. In both packings, blockers follow the unordered pairs in lexicographic index order within the supplied list.
