# Scope of the fourteen-input, eight-AND catalog

The component table covers degree multisets of possible regular receiver graphs for a 34-gate candidate. Its 10,584 rows allow multiple graph realizations, role assignments and decoder circuits. The table is not an exclusion of those circuits.

For the arithmetic table and component inventory, see README.md, degree_rows.py, component_rows.py, degree-rows.tsv and component-rows.tsv.gz in this directory. For the physical row specification and inverse, see ../geometry/fourteen34/enumeration/SPEC.md and records.py. The reconstruction control is ../calculus/fourteen34/tap-control35.json. The structural degree and branching bounds are collected in ../fourteen-eight-high-degree-cert/RESULT.md.

For a completed simple graph with q vertices, the raw bank has 28−q OR gates and the decoder has eight AND and q−2 OR gates. All 14 singleton-edge patterns must reject and all 91 endpoint unions from two distinct edges must accept. These 105 tests suffice for that graph and decoder. The empty input is dominated by a rejecting singleton and every larger positive contains a tested pair. Verifying the physical gate budget and the full truth table remains appropriate for a proposed witness.

The typed specification preserves raw-bearing mixed groups, raw-free ORs, their allowed sharing, and physical AND sharing. It describes the remaining choices. The published table generators stop at the component profile. The extractor is a control for already well-formed circuit inputs; it is not a validator of arbitrary externally supplied row records.
