# Verification receipts

The raw-first checker was independently replayed for the ranges `0 50` and `50 271`. The two runs reproduced 3,765 and 15,758 third-bank checks and zero hits. The mathematical review verified the raw-first reordering, omission of redundant operations, unrestricted sharing and distribution around the last OR for every legal circuit in the stated class.

The sole-top dual checker was independently replayed in eight disjoint slices of 17 first-stage representatives. The totals were 136 first representatives, 141,057 precursor pairs, 11 surviving pairs, 896 operand systems and zero hits. The first two slices contributed 656 and 240 systems. The independent source review also checked the leastness conditions in reductions.

For the two-top checker, an independent full-domain implementation formed maximal operand unions over all 128 unordered partitions of the eight negative rows and directly tested top pairs. It regenerated all 176 bank records and all 1,708 formal systems, including the complete 39/505/842/322 histogram. The corrected submask implementation was independently compared with all combinations of set bits for every mask 0 through 511. The v2 archive is the sole binding for this branch.

The prior minimum-size receipt is included separately. Its independent numerical run used the hashed producer binary. The standalone C++ source enumerates gate pairs directly and has no submask helper. The source, log, and unrelated depth-ten checkers were reviewed to establish that they do not use the erroneous helper from the retired two-top archive.

To reproduce the principal new checks, run the two raw-first ranges and the full sole-top checker with Node.js. Extract the corrected v2 archive in its own directory and follow its included verification instructions.

```sh
node five-or5907-first-raw.cjs 0 50
node five-or5907-first-raw.cjs 50 271
node check5907-sole-three-dirty-dual.cjs
```
