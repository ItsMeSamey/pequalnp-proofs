# Scope of the A3 replay

The sealed input archive has SHA-256 `dec0ea4a7a9cb66e3443c3608d91d62b3f4c70dcfc867ac8c3bda68f137c7b99`. All 13 files of its production manifest pass SHA-256 verification. The domain consists of seven choices of tripled mandatory owner T, the nonempty set B of compulsory points held locally at the extra eighth endpoint, and a zero or admissible local singleton baseline z. The extra endpoint is binary and line-free in its own region. The occurrence budget, at most 18 distinct raw point inputs, and normalization assumptions are those stated in high-nonempty.md.

The independent checker derives the hereditary B frontier and forced masking negatives for all seven labels using the archived geometry primitive. It computes z directly from the union of point bits on masking negatives. For every shard it checks that the exact ordered (T,B,z) keys at that shard's starting ordinal match the reconstructed sequence. It rejects repeated ordinals, gaps, unexpected records and nonzero result lists. The archive has 195, 185, 183, 184, 186, 174 and 185 cases across T=0 through T=6.

The numerical replay runs the archived solve function through a separate driver. For every completed key it checks 1 + 7 + 21 filter configurations. A separate arithmetic check compares all 43,200 relevant recipient-support threshold bits with scalar occurrence costs, across all 36 supports and eight recipients. These checks share the archived rectangle primitive and search implementation. They do not provide a separate implementation of its circuit-to-rectangle necessity proof.

Every numerical receipt records the exact case ordinal, inputs, result count, completion time and result hash. The final receipt checker rejects omissions and duplicate keys before confirming full numerical coverage.

To rerun the receipt checker, extract the adjacent raw25-high-owner-nonempty.zip into a directory named sealed beside receipt.py, then run python receipt.py. The per-case records are in first-replay.log and batches/*.keys.
