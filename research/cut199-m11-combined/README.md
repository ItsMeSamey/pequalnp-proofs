# Cut 199 at exactly eleven mixed gates

The minimum total size is 22 among single-output binary monotone AND/OR circuits computing the issued 11-vertex edge function with exactly eleven syntactically mixed gates on cut 199. The proof allows arbitrary fanout. The result concerns this specified mixed count.

Start with the [combined proof](cut199-m11-combined-outline.md). Its branch table identifies the [non-tree argument](cut199-nontree-pure-cost.md), [one-hit left-bank argument](cut199-left-general-parity.md), [rank argument](cut199-tree-port-factors.md) and [two-hit argument](cut199-tree-two-hit/PROOF.md). The full graph input is [included](pnp-official-18272-issued.lean). See the [component receipts](RECEIPTS.md) for scope and provenance.

## Replay from the extracted root

Use Python 3 and Node.js. Verify the archive manifest before executing commands. Run scans in a working copy because parity passes write tables. Producer enumeration may require substantial time.

```sh
sha256sum -c SHA256SUMS
python3 scalar_cut199_pair.py cut199-size22-mixed11.json
node cut199-kw-short.cjs
node cut199-tree-right-cost.cjs
node cut199-free-and-right-six.cjs
node cut199-six-right-joint.cjs
node cut199-tree-two-hit/verify.cjs
node cut199-left-bank-cotree.cjs 0 20 4 > regenerated-cotree.json
node cut199-left-general-parity.cjs regenerated-parity.json
node cut199-parity-full.cjs
node cut199-two-donors-split-codes.cjs
node cut199-one-pure-repeat-q5.cjs
node cut199-one-mixed-repeat-q5.cjs
node cut199-one-donor-split-codes.cjs
node cut199-one-donor-six-right.cjs
```

The parity filters read the included tables. Compare regenerated bank entries by key and minimum cost because separate shards can have different ordering. The optional historical alias driver contains an absolute producer directory. To replay it portably in the extracted root, run the following.

```sh
sed "s|Path('/workspace/scratch/site-team-11')|Path.cwd()|" cut199_alias_check.py > local_alias_check.py
python3 local_alias_check.py
```
