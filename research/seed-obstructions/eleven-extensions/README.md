# Eleven point masks with a feasible proper subfamily at eighteen mixed gates

Consider a 33-gate candidate with 18 mixed gates, eleven point boundary signals and the seven singleton line boundary signals. The connected mixed cone has one extra wire use. At most 15 original point gates are affordable. This package excludes every candidate whose eleven point signatures contain a feasible proper subfamily. Feasibility means separating every necessary point-only positive/negative obligation after arbitrary line values are granted. Inclusion-minimal eleven-mask families require a separate check.

The seven-target singleton theorem gives a lower bound of 21 point gates when all seven canonical masks are produced, even with every transversal free. The seven-signature basis contains all seven canonical masks. The 202 other eight-signature bases recover the canonical masks using at most three additional OR gates. Both classes exceed the point budget even with further boundary signals.

For each minimal nine-signature basis, singleton_charge.cpp computes an upper bound on the extra cost of recovering each target from the nine masks and actual raw primitives. A target costs at most three. Exact zero-, one-, and two-gate paths are tested with binary unions or intersections. Subtracting the total extra cost from 21 leaves 15 of 16,924 bases at budget 15. nine-double.md explains the raw witness and charge computation for every pair of extra masks. four-intersections.md proves that at least four target masks must be intersections of subsets of the eleven point masks.

For the 1,218,270 minimal ten-signature families, tenbasis.cpp retains 11,235 whose unconditional point cost can be at most 15. Its hereditary bound examines every subset of target lines. On restriction to the union of their points, each boundary output meeting every retained line in at most one point may be granted as a free transversal. If its original signature was not a raw primitive, this removes a distinct paid gate. For each retained target, a full mask requires no appended gate, a clean triple or complementary clean pairs save at least two over the three-gate fallback, and a clean pair saves at least one. Intersecting two available supersets can also save two when their intersection projects to the target. Summing the recoveries and deleted paid gates gives the lower bound from exact 3k synthesis for k retained targets. A duplicate raw singleton in the otherwise unused eleventh slot contributes no deletion charge.

For each eligible ten-basis, tenplus_ready.cpp considers all 8,191 nonzero extra masks, including repeats. An extra zero can be set to zero without changing any positive or increasing a negative. At least one mixed gate then disappears, contradicting the preceding at-least-18 mixed result. The one-extra raw negative filter uses each base signature's private witnesses to certify rejection of outside pairs as in the seventeen-mixed extension verifier. Every surviving candidate meets the four-intersections test. Cost tests precede symmetry reduction, since the sample symmetry need not preserve the raw point primitive library.

After symmetry reduction, six nine-base representatives and 272 ten-base representatives remain. Exact mixed contraction rejects all 278, with no cutoff reached. Repeated signatures remain separate mixed leaf occurrences.

Run the following with Bash, Python 3 and a C++20 compiler, using the output of the preceding irreducible-ten certificate.

```sh
bash verify.sh /path/to/seventeen-output/ten /tmp/eleven-reducible-check
```

The package includes the raw statement, authoritative nine-mask list and stage code. The preceding products consumed are the hash-checked ten-family stream and its original raw point obligation file. Mathematical dependencies include the singleton synthesis theorem, point charge and near-equality theorems, seven-line and repeated-line read-once guards, and prior 17-mixed and small-boundary exclusions.
