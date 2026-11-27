# Cut 199 paired circuit controls

Both circuits compute the same 16-edge graph function on all 2,048 assignments. Both have 22 live binary AND/OR gates, and the graph is four-cycle-free with minimum vertex cover 7. These are upper-bound witnesses and structural controls. Minimum circuit size is unproved.

| Frozen circuit | TopForm | Positive cover-inequality LHS | RHS | Left/right/mixed gates at cut 199 |
|---|---|---:|---:|---|
| raw.json | false | 11 | 12 | 0/11/11 |
| normalized.json | true | 11 | 11 | 0/10/12 |

The LHS is the minimum vertex-cover size plus the number of residual edges. Both circuits have four residual edges. The raw RHS is 6 + 0 + 1 + 5. The normalized RHS is 6 + 0 + 1 + 4. The four summands count non-centreless tops, twice the centreless tops, junk ANDs, and orN outside lam. The raw control has clean AND gate 4 strictly below AND gates 10 and 13. The normalized control has no such pair. All gate IDs in scores.json are zero based.

## Sources and construction

The raw circuit is a byte-for-byte copy of /workspace/scratch/site-team-11/cut199-size22-mixed11.json. Its graph is the graph decoded from /tmp/pnp-official-18272-issued.lean. The normalization was proposed by the site-team-11 lead and applied by build.py to this raw list. It preserves all raw operation and input order before the collector except for the removed wire 16, and makes the collector a balanced binary tree on six terms. The base verification implementation check4186.py is copied from /workspace/scratch/site-team-05/check4186.py. The independent team-07 r07 verifier confirmed the full-cube values, both ledgers, cut counts and all offending pairs against the official edge list.

In the raw circuit wire 15 computes the edge P = x5 AND x9. Wire 16 computes x8 OR P. The normalized circuit replaces each use of wire 16 with x8 and ORs P directly into the output. On inputs with P false, the substitution preserves the old computation. On inputs with P true, the graph function is true because 5–9 is an edge, and the new collector outputs true. Removing one OR and adding one collector OR preserves size.

Both circuit files encode gates as triples [isAND, leftWire, rightWire], with false denoting OR. Wires 0 through 10 are primary inputs and gate j produces wire 11+j. The cut’s left side is {0,1,2,6,7}. The output is a wire index. The raw control's embedded audit is original metadata. scores.json contains a fresh detailed ledger for both circuits.

## Replay

From the extracted directory run the following commands with Python 3.

```sh
sha256sum -c SHA256SUMS
python -B replay.py
```

To reproduce the normalized bytes, run `python -B build.py`, then verify the checksums again. The two standard-library scripts and the included checker require no external data for replay.
