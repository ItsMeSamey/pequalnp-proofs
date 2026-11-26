# Exact gate count for bipartite mask 7879121

The minimum is **10 gates** for a fan-in-two AND/OR/NOT circuit on the one-per-shore promise. Mask bit 5u+v specifies the output on row u and column v. The ten-gate witness in baseline10.json agrees on all 25 inputs.

The twin reduction in twins.md preserves unrestricted fanout and reduces the lower bound to 25 input supports on a 4×4 table. The C++ and Python implementations exhaust the same 75 support and gate-budget combinations. Both reject every combination at size nine. A neighboring function with a nine-gate witness provides a positive search control. The two receipt checks run with Python 3 from their respective directories using `python audit.py` and `python check_receipts.py`.

This finite computational lower bound addresses the positive existence question in desk unit L-meta-20555. The archive contains the programs, traces, and applicability arguments. A Lean proof of the lower bound remains open.

Control10.lean proves the ten-gate upper bound against PEqualNP.Defs. The producer recorded the source, compiled object and compiler log in Control10.sha256. The independent register scope review covers the lower-bound search.
