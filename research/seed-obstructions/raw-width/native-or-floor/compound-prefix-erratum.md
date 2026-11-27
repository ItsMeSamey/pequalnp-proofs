# Four missing raw operands in the physical prefix enumerations

The 19-AND, 14-OR exclusion at area 33 is **pending for the single-compound banks 7 and 17 and the paired-compound bank 115**. The physical third-prefix enumerator in `physicalK.hpp` skips four raw signals whose positive support consists of a singleton. Each is an eligible operand of K. Introducing a clean AND to simulate a skipped signal can exceed the gate budget. A suffix check on the supplied prefixes therefore leaves open the prefixes that the enumerator missed.

| Affected producer artifact | SHA-256 | Scope |
|---|---|---|
| `native-or14-single-third.zip` | `241ad085ea805aa017550af3d68869bd24f1396a8e10d25b2d1a97ff9299689c` | Incomplete physical prefix enumeration for banks 7 and 17 |
| `native-or14-paired-third.zip` | `3ed3caae73aa695a8a3009ed5761c2f4f0fe59adeafe1102bd83db74df09105d` | Same omission for bank 115 |
| `native-or14-single7-17-suffix.zip` | `4022e19ee4d83e5a5d96716c414a8e54ff6d543c9ffc9f921be541c65db2bf14` | Suffix result conditional on the supplied prefix list |

## Withdrawal of the original literal-bank signoff

The verifier also withdrew the integrated literal-bank signoff in `review-selected-literal-h19.zip` (SHA-256 `6082ece0910dace9a7defb860e7d86382a66fd164418ecea7e7f9684be07e1e4`), published in commit `5b668c0f8`. That proof restricted each third-gate arm to at least two positive rows. The restriction applies to a paid dirty AND, but four degree-one bare raw point inputs are legitimate operands. The checks on the 306 recorded states and 16 surviving suffix pairs retain their original scope. The archive does not establish that its prefix list is exhaustive. Its conclusion that a minimum-area, minimum-AND literal representative at area at most 33 has at most 18 ANDs is **on hold**.

This withdrawal corrects the assessment of the literal-bank signoff in erratum commit `e0dfe6714`. The all-bank 14-OR lower bound in `9e14ce04d` retains separate coverage. A candidate unrestricted literal-bank 15-OR proof, `native-unlimited-literal-or15.zip` (SHA-256 `d727e86e99f65dbe71aad1d5e84983cea5a98da7c938ef391ee1ced42afd7d16`), enumerates all 28 singleton K traces. Coverage and its connection to the corrected conclusion await an explicit verification receipt. Each compound-bank corner likewise requires complete prefix and suffix coverage or an operand-elimination proof that preserves both budgets.

## Independent replacement for the literal bank

The subsequent verifier receipt `review-native-or-operand-coverage.zip` (SHA-256 `7a567ee6a0b226a193ec748c1d37322cb9bf27cf2d96c98d9d00920473036ad2`) checks all raw and paid operands in the replacement literal-bank enumeration. The 306 resulting H,J rows match the independently checked 16-orbit suffix input. Together with `native-unlimited-literal-or15.zip`, this establishes **at least 15 OR gates in the literal bank with any number of AND gates**. Thus an area-33 literal-bank separator has at most 18 ANDs. The original integrated prefix proof remains withdrawn.

## Independent replacement for single-compound banks 7 and 17

Both single-compound banks require **at least 15 OR gates with unrestricted AND count**. The repaired enumeration retains raw operands with a single positive row and uses OR-preserving clean extraction for paid singleton products. The early collector bound and the two suffix checks allow arbitrary AND count. The transport certificate maps bank 7 to bank 17, including the supplied compound signal.

The released envelope `native-unrestricted-single-or15.zip` (`dd8b55c0`) contains the corrected prefix (`d543f2bd`), original suffix check (`4022e19e`), supplemental suffix replay (`ca61c8b0`) and transport (`dbf06eb4`). The independent original-operand map is `single-original-operand-map.zip` (`f42d8b09`). Running `single-union-audit.py` (`51f3a80b`) on the original suffix, corrected prefix and supplemental suffix archives in that order verifies that the 2,218 old and 58 added rows form all 2,276 corrected rows. The supplemental rows contribute 28 signed inventories, all among the 369 already checked. The proof for these two banks uses the corrected enumeration. The earlier incomplete prefix remains withdrawn. This entry leaves paired bank 115 pending.

## Complete four-bank replacement

The all-four dispatch `native-unrestricted-four-or15.zip` (`26d89a6b`) and its independent aggregate review `four-bank-independent-review.md` (`1db87ace`) close the paired bank as well. The unrestricted prefix retains all original singleton operands. The 52,717 paired prefix records yield 8,926 distinct signed inventories. The suffix ledgers cover the first 6,500, the next 2,378 and all 48 additional inventories. A clean dispatch replay reproduced the stored audit log, including terminal outcomes for all 623 forwarded high-range cases. The dispatch verifies stored stage results. Instructions for regenerating the individual computational stages are in the constituent archives.

**Each of the four native banks 0, 7, 17 and 115 requires at least 15 binary OR gates, allowing arbitrary numbers of AND gates and arbitrary fanout.** An area-33 separator in any of these banks therefore has at most 18 AND gates. This result leaves existence at area 33 open.
