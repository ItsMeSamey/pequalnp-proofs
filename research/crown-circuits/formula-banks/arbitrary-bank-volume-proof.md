# Arbitrary independent OR banks followed by a monotone formula

**Theorem.** Compute the twelve paired signals zᵢ = xᵢ ∨ yᵢ. Choose any collection of nonempty subsets of these signals and compute their ORs independently. Singletons cost zero gates. Evaluate any binary monotone formula on these bank outputs. The minimum total size for the 12-crown is 41. A label may participate in arbitrarily many banks, and different bank subsets may overlap. This cost model counts independent OR trees for the bank outputs and single-use internal gates in the formula tail.

Let R be the total number of incidences between labels and banks, and s the number of banks used by the formula. Delete unused banks and duplicate input occurrences within a bank. If bank v occurs dᵥ times in the formula, set E = Σᵥ(dᵥ − 1). The circuit size is

    12 + (R − s) + (Σᵥdᵥ − 1) = 11 + R + E.

The support of label i is the set Sᵢ of banks containing it. The twelve supports form an antichain. If one were contained in another, their distinct-label union would give the same bank input as the larger support alone. No support is empty. A label with singleton support {v} therefore has private bank signal zᵢ at v. If dᵥ ≥ 2, divide the occurrences between two names for this signal, each used nontrivially. This changes neither the computation nor its physical cost. R increases by one and E decreases by one. A remaining singleton support has one true occurrence and, by the arbitrary-formula certificate bound, its event occupies at least half the space. At most one such label can occur.

Without a remaining singleton set p = Σᵢ(|Sᵢ| − 2). A total size at most 40 gives R=24+p and E ≤ 5−p. With one singleton, set it aside and sum the excess over the remaining eleven supports. Now R=23+p, E ≤ 6−p, and those eleven labels must fit in measure at most one half.

If p=0, all supports have size two apart from the possible singleton. The arbitrary-formula endpoint proof applies. For the remaining singleton, one may append a private unused endpoint at zero cost to put it in exactly the earlier graph notation.

If p>0, at most p of the remaining supports have size larger than two. Apply the coarse pair-label volume bound to at least 12−p pairs without a singleton, or at least 11−p pairs in the singleton case. The heavy–light degree bound still applies because fixing the heavy vertex and its three hypothetical light neighbors uses only the pair tests for those labels. At least one support of size greater than two also has a nonempty certificate event and therefore contributes positive measure beyond the pair bound.

| Available measure | p=1 | p=2 | p=3 | p=4 | p=5 | p=6 |
|---|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 19/16 | 25/16 | too few slots | too few slots | infeasible |
| 1/2 | 5/8 | 3/4 | 13/16 | 17/16 | 5/4 | too few slots |

The entries minimize the sum of the cheapest pair-slot bounds over heavy weights with the reduced surplus, allowing every heavy pair. Even where the pair bound equals one, at least one large support requires additional measure. Every p>0 is therefore excluded. The grid construction gives the matching upper bound.

The verifier arbitrary_bank_volume.py uses exact fractions and the helpers in endpoint_volume.py. The p=0 case uses arbitrary-formula-volume-proof.md and arbitrary_formula_volume.py.
