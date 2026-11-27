# Constructive frontier normalization

This source-only package uses Python 3.10 or later and its standard library. It checks binary AND/OR graph circuits by exhaustive evaluation. See [the argument](constructive-frontier.md) and [the score definitions](score.md). The package supplies mathematical reasoning and executable checks. It contains no Lean kernel certification.

Extract the ZIP and run the following from its directory.

```sh
python3 -B verify.py
python3 -B constructive-abi-audit/convert.py fixtures/fold5.input.json -o result.json
```

Use a finite simple graph with at least one edge, a full input count including isolated vertices, an ordered list of binary gates and a valid designated output wire. Inputs are wires 0 through n−1, and gate i is wire n+i. Both pins must name earlier wires. Repeated pins are allowed. Edges are endpoint pairs; reversed duplicates denote the same edge. Gates accept Boolean triples (true for AND), operation-name triples, or objects with op and inputs. For inputs without an n field, pass `--n N`. Tap banks require explicit terminal gates and an output before conversion. An early designated output is permitted. Dead gates can yield an immediate shortening.

The result includes the output circuit and designated wire, sizes, initial and final scores, and the selected wire at each stage. These indices refer to the current compacted circuit. The shorter branch may stop before TopForm. [Fixture records](manifest.json) and expected outputs cover both branches. SHA256SUMS covers all other package members.
