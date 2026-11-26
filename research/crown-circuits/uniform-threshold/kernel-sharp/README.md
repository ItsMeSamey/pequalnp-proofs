# Sharp square-root lower bound for threshold two

For every n ≥ 4, a binary monotone circuit C computing threshold two on the full Boolean cube has size at least 2n + (√(8n − 7) − 7)/2. The theorem applies to unrestricted fanout. The same lower bound holds for the minimum circuit size.

Lean 4.36.0 compiled the native real bound, the integer bound and the minimum-size bound. Each endpoint reports propext, Classical.choice and Quot.sound. The manifest lists the 109 project and local sources in dependency order with SHA-256 hashes. The producer manifest records their original locations. An independent clean replay recompiled all 109 sources, including six PEqualNP modules. Every local dependency resolved to an earlier fresh object. All three axiom reports matched byte for byte. [Independent replay receipt](independent-replay/README.md)

[Native theorem statements](sources/ThresholdPublicSharp.lean) · [Axiom receipt](axioms.log) · [Portable manifest](ThresholdPublicSharp-manifest.tsv)
