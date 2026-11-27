# Four productive ORs cannot cover the target in seven taps

For the eleven masks in L-meta-18272, two independent programs searched exactly four productive OR gates with intersections available at no cost. Both enumerated 85,164,145 fourth states across 55 first branches. Neither found a cover of all 16 positive rows using at most seven clean terminal pairs. At every first branch the raw independent count equals the producer count, so every signed count adjustment is zero.

The previous complete result, included at `reference/three-or-bound.tar.gz`, excludes zero through three productive OR gates even with eight terminal pairs. Combining the results, **any witness using at most seven terminal pairs requires at least five productive OR gates**. At eight intermediates and seven pairs, the issued minimum of three AND gates then forces exactly five physical OR gates and three AND gates. This package leaves that five-OR case open and does not supply a Lean kernel proof.

## Verify locally

Run `./check.sh` from an extracted copy of this archive with GNU sha256sum, Bash and Python 3.8 or newer. It checks the distribution manifest, binds the independent source masks to the issued inputs, checks every second-level receipt and its per-shard third/fourth totals, and executes the original frozen producer verifier in checked mode. Exit zero and final JSON status `verified` indicate both receipt sets agree. No compilation or enumeration is required for this integrity and receipt check.

The independent archive includes the original replay source, method description, controls, and all 55 sets of semantic zero-hit receipts. Its SHA-256 is `b75500603ca8aa1051e1a59458bbd61860958e7b11794ad996fafd76cc7b3cb5`. Team 07 supplied its reviewed-shards array with SHA-256 `11fbd0ff8c2f8132aef9a7e891ec65281ee7a61837f91e4ce9627e37867e6952`. The confirmation wrapper contains those original 55 rows unchanged. The portable check uses the supplied archive directly, independently of the historical paths in the archived comparison script.

## Provenance

The issued statement SHA-256 is `9ec4bd7fce25977e79676fd87f567c30812b34f80a264e9df1a9aeb6d972f84b`. The frozen four-OR producer-only archive had SHA-256 `c223da52e146b59de44f9d214ba8d30aa9216ea703dc343dbe699f352cb7c51a`. Its README, retained as `PRODUCER.md`, describes the relaxation, canonical ordering, historical shards 0 and 32, and the then-pending evidence. Its original file manifest is `producer-files.sha256`. Use the distribution-level `SHA256SUMS` for the merged package. The earlier three-OR archive has SHA-256 `fb69e524041d9145fb654512f36bd3979655d2ff2b1548d64d9f6ee250c1db4a`.

The canonical producer receipt-set digest is `8fd833b9b498d0f8f12cfecdc45a1f526e84633e18ee741dcd758459e0280898`. The zero-hit conclusion is computational and applies to the stated projection, productive-OR count and terminal budget.
