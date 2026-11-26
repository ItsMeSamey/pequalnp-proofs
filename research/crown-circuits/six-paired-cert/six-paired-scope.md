# Six-AND lower bound in the paired twelve-label crown

The paired construction begins with twelve gates z_i = row_i OR column_i. Its tail computes threshold-two on the twelve z inputs when tested on singletons and pairs. A forty-gate paired circuit would have a tail of at most 28 binary gates. With six ANDs its transposed tail permits at most seventeen binary unions.

Choose a size-minimal representative and minimize its singleton-hot ANDs secondarily. The nonempty deficits of its twelve paired receivers are pairwise disjoint on 64 complete resolutions. In terminal normal form at least one clean AND feeds the output through the terminal OR tree. A clean terminal comparison has full activation. A dirty AND cannot have full activation because its hot singleton has a rejecting resolution.

| Clean terminal ANDs | Dirty ANDs | Certificate |
| ---: | ---: | --- |
| 1 | 5 | six-single-terminal-proof.md and six_single_certificate.js |
| 2 | 4 | six-multiple-terminal-model.md and six_middle_certificate.js |
| 3 | 3 | Same middle-terminal certificate |
| 4 | 2 | Same middle-terminal certificate |
| 5 | 1 | six-one-dirty-proof.md and six-one-certified-replay.sh |
| 6 | 0 | Existing clean arbitrary-axis paired-bank theorem, reductions/fivebank/reverse-bank-proof.md and general-17.out |

The one-terminal bypass invokes the existing five-AND lower bound. Terminal normalization and removal of direct receivers are inputs to these finite tables. The separate reductions/seven/direct-split.md proves a bounded direct-receiver solution specializes to eleven variables and then yields a twelve-variable no-direct representative by adding a split variable. The tables check the no-direct, minimal-dirty branch.

The order audit and fallback are in six_causal_precursors.js, six_causal_audit.js, six-causal-ledger.ndjson, and six-causal-corrected-optional.ndjson. selector-order-audit.md covers the four- and five-AND programs. The corrected optional one-terminal replication includes the 60 exceptional chronological rows.

The complete tables rule out a 40-gate paired six-AND circuit under those reductions. This is a finite computational proof outside the Lean kernel. Unrestricted asymmetric circuits, other AND counts, and the full twelve-crown minimum require separate arguments.
