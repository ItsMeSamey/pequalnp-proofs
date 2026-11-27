# Exact size of the five-by-five relation with mask 28121121

The minimum is **10** for the fan-in-two AND/OR circuit model on the original one-per-shore input domain. The desk's L-meta-21246 asks whether a circuit of size at most **9** exists. The checked lower theorem proves the negation of that statement. A ten-gate construction gives the matching upper bound. [Lean source](https://github.com/ItsMeSamey/pequalnp-proofs/blob/b7ab46e36bc56b98705340fda7b306f203be87bc/research/one-hot-circuits/mask-28121121/L_meta_21246.lean) · [Axiom report](./axioms.log) · [Ten-gate construction](./control10.json)

The source imports only `PEqualNP.Defs`. To verify the archived digests, decompress `L_meta_21246.olean.xz` into a temporary copy of this directory and run `sha256sum -c SHA256SUMS`.
