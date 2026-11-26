# Every size-33 residual separator requires at least 23 mixed gates

Every normalized L-meta-18968 separator with at most 33 binary AND/OR gates requires at least 23 mixed gates. The earlier theorem in synthesis_new/twenty-one-summary excludes up to 21. Suppose exactly 22 mixed gates remain, and let P and L count the distinct physical point and line wires entering their reachable cone. At most eleven pure gates remain, P≥11 and L≥7. The cone has 23−P−L excess reads, so P+L≤23. A cut with P=11 needs at least nine pure point gates, excluding L≥10 at that width. The table exhausts all remaining widths. Paths are relative to /workspace/scratch. Detailed budget arithmetic is in syn_bounds/twenty-two/README.md. Unrestricted size-33 existence remains open.

| Point width | Line width | Principal closed-cell certificates |
|---|---|---|
| 11 | 7 | syn_mitm/w11-seven-five/w11-seven-five-roles.zip and w11-l7-ten-minors.zip |
| 11 | 8, 9 | syn_bounds/twenty-two/w11-eight-m22.zip and w11-nine-m22.zip |
| 12 | 7 | syn_dual/twelve-seven-four.zip |
| 12 | 8 | synthesis_new/three-cuts-cheap.zip, three-cuts-eight.zip, three-cuts-nine.zip and syn_quotients/m22_ten_pair_cert.zip |
| 12 | 9 | syn_verify/twenty-two-nine-point-nine.zip and syn_quotients/m22_w12nine_cert.zip |
| 12 | 10, 11 | syn_verify/twenty-two-ten-line.zip and twenty-two-eleven-line.zip |
| 13 | 8 | Price and extra-mask partition in the next section. |
| 13 | 9 | syn_cover/thirteen_nine/W13L9-true-through-seven.zip, W13L9-eight.zip, W13L9-nine-e4.zip and W13L9-nine-complete.zip. |
| 13 | 7, 10 | Seven-line three-surplus theorem and syn_cover/thirteen_ten/W13L10-verified.zip |
| At least 14 | All feasible | Width-independent seven/eight-line results and syn_bounds/twenty-two/four-private-uniform.zip |

### Thirteen point slots and eight line slots

The physical line interface contains the seven raw singleton signatures and an additional mask E. A genuine E costs at least |E|−1 line gates. If E is zero or a duplicate singleton, simplify after substituting zero or the literal line. The earlier seven-line bound then applies. Empty point signatures clamp to zero. For arbitrary repeated nonzero point signatures, syn_quotients/dup12_cert.zip supplies the physical-versus-optimistic transfer and the remaining 896 comparisons. The quartet production also checks padding directly.

- Through point price seven use syn_sat/w13-price34.zip, w13-price5.zip, w13-price6.zip and w13-price7.zip. The seven-paid stage checks 700,570 cases from 6,908 point orbits. The raw primitive library is tested in each physical orientation before quotienting.
- For |E|=2 use syn_sat/w13-line-pair.zip at every price through ten. The corrected virtual variant is syn_sat/w13-line-pair-virtual.zip. Point price ten admits no larger E.
- At point price eight, |E|≤4. For triples, synthesis_new/w13-l8-eight-triples.zip checks 427,535×35=14,963,725 cases, 3,575 pass the placement screen and all fail the mixed check. For quartets, syn_sat/w13-price8-quartet.zip covers nine disjoint shards of the same 427,535-row point domain. Removing 6,851 cheaper distinct banks leaves 420,684 point orbits and 14,514,325 simultaneous quartet/point cases. All fail in 421,828 group checks. The 5,993 physical padding rows give 264 incremental orbits and 15,872 three/four-label cases, also excluded.
- At point price nine, |E|≤3. For three original specials, apply the unrestricted-width promoted theorem in syn_near/k2/package/README.md with promoted.py and width.py. At P=13, g=9 and δ≤2 it has effective parameter 25−(13+9)−δ≥1. At four specials use syn_sat/w13-triple-disjoint.zip and w13-triple-shared.zip. Five specials split into outside width b≤8, b=9 or 10, and b=11. Use syn_sat/w13-five-b8.zip, w13-five-multi.zip and w13-five-b11.zip respectively. The six-charge argument is in syn_sat/four-seed.zip and syn_sat/w13-triple/SEEDS.md. The b=9,10 endpoint computation rejected all 190,272 configurations. The underlying two-surplus physical placement is also recorded in syn_mitm/twelve-eight/w12-l8-expensive.zip.

For larger widths, the seven/eight-line reductions are in syn_mitm/seven-line-k3.zip, syn_dual/eightplus/README.md and synthesis_new/nineteen-final/README.md. Read-once L=9 uses synthesis_new/twenty-summary/nine-readonce.md for the generic reconstruction and syn_bounds/twenty-two/four-private-uniform.zip for the four-group cases. The latter would need at least eleven pure point gates on top of two line gates. At W13L9 cost eight, all 870,941,412 new point/line pairs are covered. The unfiltered final price-nine pentads cover 1,126,710 comparisons and reject all 1,660 exact fallbacks. These W13L9 checks no longer require the optional primitive-orientation reduction in the final orbit.

All principal authoring checks are complete. The W12L8 price-nine independent full replay produced 42,918→9→0. Reviewers independently checked the W13 two-surplus placement and cohort transfer, four-seed cost lemma and virtual-pair correction. Complete separate numerical reruns are not yet claimed for every W13 archive. A fresh W13L8 price-eight triple numerical replay is active, and the last quartet shard partition is under independent audit. The budget grid at mixed count 23 is separate in syn_bounds/twenty-three/README.md.

## Independent verification coverage

All 50 dependency hashes were verified at publication. The producer completed the full grid. For W13/L8 the independent review reconciled the complete quartet shard ledger and the padded physical cases, regenerated the domains, and replayed a deterministic sample of 875 of the 14,514,325 quartet orbits. W12/L8 price nine was independently replayed from 42,918 cases to nine survivors and then zero. At price ten the producer completed all 274,556 cases and an independent source and ledger audit passed. A full independent numerical repeat of price ten remains pending at this release. The earlier floor of 22 mixed gates is in commit 36b68f82. Run `sha256sum -c SHA256SUMS` in this directory before replay.
