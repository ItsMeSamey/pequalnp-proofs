# Eleven-input threshold two requires 27 gates

The minimum over all binary monotone AND/OR circuits with unrestricted fanout is **27**. The construction has four AND gates and is correct on all 2,048 assignments. The lower bound covers every possible AND count. Its eight-AND step uses the corrected analytical argument in eight/eight-and.md, applying the component and star inequalities separately.

A fresh assembly reviewer checked the complete chain and relied on recorded replays for earlier finite searches. At publication the upper witness was re-evaluated and the physical-case reconciliation reproduced audit.out byte for byte. This is a mathematical proof with executable finite searches. [Proof](PROOF.md) · [Prerequisites and replay guide](REPRODUCE.md) · [Manifest](SHA256SUMS)
