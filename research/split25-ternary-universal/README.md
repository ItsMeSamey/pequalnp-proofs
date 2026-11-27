# A free ternary dictionary in flat signed CNF on split25

Fix the 115-gate prefix supplied for L-meta-20579, shard 53. Its 25 ordered ports are the old coordinates. Choose any three ports and grant every Boolean predicate on them, including complements, without charge. For every one of the 2,300 choices of support, a single flat signed CNF for the target requires **at least 56 additional physical gates**. This exceeds the tail budget of 55 by at least one gate. The statement covers cascades whose output depends only on that designated triple.

The CNF is an AND of OR clauses over signed individual old coordinates and the free dictionary predicates. Binary gates may share partial disjunctions and fan out. A negative old literal outside the free dictionary requires its input NOT gate. Arbitrary mixed multilevel circuits fall outside this family.

## Replay

From the extracted directory, run the following command with Python 3.10 or later. No solver, network connection, or external data file is required.

```sh
python3 -I -B check.py
```

The two frozen JSON checkpoints retain the original negative endpoint lists. The first supplies zero-based support indices 0 through 1922, and the second supplies indices 1923 through 2299. The indices refer to lexicographically ordered triples of distinct coordinates from 0 through 24. The checker rejects gaps and mismatched thresholds and checks the original byte hashes of both checkpoints.

The public statement supplies the 32 target row masks. On cell (r,c), the checker activates raw inputs r and 32+c, computes every prefix wire, and compares the target bit and 25-bit signature with the corresponding row in the manifest. It also checks the 115-gate prefix and the first internal NOT's diagonal mask 0x35. Every certificate cell is a **physical index 32r+c**. Two different cell IDs with the same 25-bit signature cannot count as distinct endpoints in one packing.

## Pair certificates and clause cost

For each support, the certificate gives k negative cells. For every pair with signatures a and b the checker finds an actual target-positive cell with signature t satisfying both conditions below.

1. On every coordinate where a and b agree, t shares their value.
2. On the entire designated triple, t matches one of the two endpoints.

If a clause is false at both endpoints, every old literal in it is also false at t. Every dictionary literal in the clause is false at both endpoint restrictions and hence at the matching restriction of t. The clause would be false at a positive cell. Thus every valid clause can exclude at most one packed negative, and k different clauses are necessary.

Both values of each old coordinate occur on positives. No single old literal can be a valid clause. Further, all dictionary-only unit clauses together can exclude at most one packed endpoint. If they excluded two, take their pair blocker t. Its restriction agrees with one endpoint, so the particular unit excluding that endpoint would exclude t. At least k−1 selected clauses therefore require distinct binary OR outputs. Joining k distinct selected clause outputs in one flat conjunction requires at least k−1 binary ANDs, even with sharing.

The checker derives 18 distinct decreasing coordinates from target-positive signatures p and target-negative signatures obtained by changing only one bit of p from 0 to 1. For a coordinate outside the chosen support, all free dictionary values agree on these two signatures. Without that old coordinate's negative literal the expression is nondecreasing in it. Each such coordinate requires its own unary NOT. If d of the 18 lie in the chosen triple, the tail cost is at least **2k−2+18−d**. No charge is assigned to evaluating any dictionary predicate.

| d | Number of supports | Smallest certified k | Minimum tail bound |
| --- | ---: | ---: | ---: |
| 0 | 35 | 20 | 56 |
| 1 | 378 | 21 | 57 |
| 2 | 1,071 | 21 | 56 |
| 3 | 816 | 22 | 57 |

## Release commitments

The manifest, public task, original checkpoints, and checker sources are listed in SHA256SUMS. The checker prints an additional digest of the independently reconstructed rows in physical cell order. It uses unsigned big-endian 16-bit cell ID, 8-bit target label, and 32-bit signature after the domain tag `split25-rows-v1` followed by one zero byte.

A separate proof-trace digest begins with the domain tag `split25-universal-full-v1`, one zero byte, and the binary row digest. For each support it hashes its index, endpoint count, sorted physical negative endpoints, and the least compatible physical positive cell ID for each endpoint pair in that order. All of these integers are unsigned 16-bit big-endian. This normalization permits independent comparison without requiring producer and verifier to choose the same representative of a signature.
