# Seventeen mixed gates on ten point signals and seven raw lines

The checker takes the original formal statement, the refined irreducible point families, the ordered nine-mask bases, the distinct extensions of those bases, and their repeat-or-zero extensions. Each extension row contains a one-based base index, the tenth mask, and the point-cost lower bound. It rebuilds the ten-mask multiset before applying any symmetry. The upstream point-cost and family-generation proofs establish why these three inputs cover the remaining cases.

Run with Python 3 and a C++17 compiler. The five input paths below are placeholders for the corresponding release files.

```sh
python verify.py L-meta-18968.json refined-all.txt nine.txt geom_survivors.txt dupgeom_survivors.txt
```

The wrapper checks the SHA-256 digest of the formal statement, decodes the 28 positive and 245 maximal negative raw rows, and verifies each of the 24 permutations used to identify equivalent families against those two row sets. Removing redundant extension histories leaves 26,664 distinct ten-mask families from the 26,754 distinct-mask extensions. Repeated masks retain their separate input positions.

| Family source | Distinct families | Orbit representatives |
| --- | ---: | ---: |
| Irreducible, point lower bound at most 16 | 23,274 | 1,123 |
| Distinct extension of a nine-mask base | 26,664 | 1,713 |
| Repeat or zero extension | 1,122 | 65 |

Replace each point signal by the OR of the point coordinates in its singleton signature. Every residual positive has a singleton point input, so this preserves all its boundary values. At a negative the substitution can only decrease a monotone signal. Thus a separating circuit on the original point signals must also separate on the canonical signals. Each line input is the actual raw bit.

There are seventeen leaf occurrences before any gate and seventeen binary mixed gates. Counting operand uses in the connected output cone leaves one extra use beyond the single-use tree. The checker starts from the seventeen input signals. Each step consumes two available signals, forms their AND or OR, and adds the result. Once during construction it may retain one operand for a later use. This enumerates every possible position for the extra use, including reuse of an intermediate. Gates with two operands from the same unmixed side are excluded. An idempotent gate with two identical physical operands can be removed. If this is the only repeated use, the resulting sixteen-gate tree can also be padded after its output, or handled by the seven-line read-once bound.

Every positive/negative pair must be distinguished by a current frontier signal that is one at the positive and zero at the negative. A pair distinguished by both selected operands survives either binary operation. Only a pair distinguished uniquely by a consumed operand can be lost. The checker records the positive and negative projections of those private pairs. For AND, the other operand must accept every relevant positive. For OR, it must reject every relevant negative. Retaining the endangered operand also preserves the distinction.

After spending the extra use, the suffix is a read-once formula in the current signals. A minterm and a maxterm of a monotone read-once formula meet in exactly one variable, by induction on the root operation. Here a maxterm is a minimal set of inputs which, when fixed to zero, forces rejection. A private distinction at a positive forces its wire into every compatible minterm. A private distinction at a negative forces its wire into every compatible maxterm. If two wires are mandatory on one positive and on one negative, the remaining formula cannot be read-once. This applies to the distinct frontier positions even when two positions take equal values on the sampled rows.

The frontier state includes the multiset of sampled truth tables with ancestry-side tags and the number of extra uses spent. Equal states have the same possible continuations. The C++ program has no search budget. It accepts only when every frontier disappears before a separator is produced, emits the extinction depth for each case, and returns a failure status if a complete separator survives. The Python wrapper checks the number of reported results against the independently regenerated representatives.
