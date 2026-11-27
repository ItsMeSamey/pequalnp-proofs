# First-fork coloring and conflict witnesses

[The theorem](THEOREM.md) bounds the number of distinct fork producers in signed fan-in-two circuits from directly observed partial truth-table data. In the included fixed-bank example the conflict graph has chromatic number three. Every implementation must therefore have at least two distinct forks at any gate budget.

Run the standalone checker from the extracted directory using Python 3.10 or later. No packages or network access are needed.

```sh
python3 -I -B check.py
python3 -I -B audit.py
python3 -I -B audit_wedges.py
```

The checker evaluates the control and all eight joint output overrides on each of 1,024 cells. It checks 15 donor-necessity certificates, all 105 donor pairs, the complete edge set, the triangle and the proper three-coloring. Inputs include the mathematical statement from unit L-meta-20579, the 181-gate control for range 53, and the certificate files. The statement with a terminal LF has SHA-256 e233b9b26bab1a8856b41abefce91ad2660f5139effd3df1ad8e11582240f816. Gates in the control use 64 input wires. Gate j writes wire 64+j. The original output is 243 and the first qualifying NOT outputs diagonal mask 0x35.

The independent full-table audit exhausts the 1,890 one-gate cases with its configured three donors, pin lists and labeled taps. Seed 725 adds 6,000 random and 1,200 planted/De Morgan cases. It checks 9,090 circuits and 1,327 strict-square conflict edges. The replay digest is 189214bcee865a42bdc892a3dabfc6c6417acc7fefad921a7a037b0b2670dbac.

The supplemental wedge audit uses seed 2057953 with partial promises and read-once signed aggregations. Its 1,601 cases give 174 wedge edges across 58 circuits. Replay digest 8b19dae147513772c189eade51e81c410c0595285fcafae9dec9bf8e91f028a5. Both tests supplement the mathematical proof. The included control exceeds the unit's 170-gate target and serves only as input to this local analysis.
