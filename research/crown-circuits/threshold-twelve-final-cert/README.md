# Exact minima for twelve labels

Threshold two on twelve Boolean inputs requires **29** binary monotone gates. The twelve-label physical crown requires **41** on the promise of one selected row and one selected column. Both minima allow arbitrary topology and fanout.

[Proof and prerequisite commits](RESULT.md) · [Upper-bound checker](upper.py) · [Source and receipt hashes](SHA256SUMS)

A fresh assembly reviewer audited the dependency chain, the transfer between the two problems, the upper witnesses, and the final graph classification using an independently implemented census. The assembly review relied on recorded replays for earlier large finite searches. For example, the ten-input prerequisite's original recurrence was replayed on 25,601 profiles, and a separate implementation matched all their budgets and verdicts. The proof combines mathematical reductions and finite computations. The previously kernel-checked OR bound is one component. The earlier unrestricted eleven-input bound is in commit 05d498a339429f855b7afa64d8e3ad3822444bc8.

Run `python upper.py` to verify the 29-gate construction on all 4,096 assignments and its 41-gate paired extension on all 144 promised crown cells. Run `sha256sum -c SHA256SUMS` to compare the proof package with its release manifest.
