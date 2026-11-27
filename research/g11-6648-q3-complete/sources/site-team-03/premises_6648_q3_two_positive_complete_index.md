# Two physical dirty-reading ORs, both raw-positive, at q=3

In the size-21 least original L-meta-6648 TopForm circuit, assume x=3 has sole reader A=x∧S, A clean, j≥3, q=3. Exactly two distinct physical ORs below the tops directly read a dirty AND; each has one such pin and one raw-positive pin. Their dirty pins can be the same gate. Under the original 19/15 labelled-card classification, original G11 corner footprints, and indicated H-batch inequalities, the original residual count satisfies U≤2c+j+3 for every c and j in scope.

A tap is a path consisting entirely of ORs from one of these physical outputs to S. The number of visible labels refers to the original OR-reachable raw labels of S. These lie in {6,7}. The other paid OR can be pure or inherit mixing; no disequality, disjointness or privacy of unrepeated donor ancestors is assumed.

| Visible labels | Physical taps or donor relation | Proof |
|---|---|---|
| 0 | Empty raw S, same donor | premises_6648_q3_empty_repeated_donor.md; sparse one-exception argument and original singleton transfer |
| 0 | Empty raw S, distinct donors, c=1 | premises_6648_q3_empty_c1_distinct_donors.md; F(1,1)≤2 and F(1,3)≤5 |
| 0 | Empty raw S, distinct donors, c≥2 | premises_6648_q3_empty_distinct_donors_all_c.md; original named readers and sparse star counts; c=0 is impossible since A is centreless |
| 1 or 2 | Both physical outputs tap | premises_6648_q3_two_direct_taps.md; one-exception bounds at 1 through 5 groups |
| 2 | Zero taps | premises_6648_q3_full_S_zero_taps.md; common-OR card proof |
| 2 | One tap | premises_6648_q3_full_S_one_tap.md including final c=0 supplement |
| 1 | Zero taps | Impossible because the pure singleton disjunction misses the hidden neighbor |
| 1 | One tap, all except nested j=3,c≤1 with 2 or 3 near stars | premises_6648_q3_visible_two_positive_index.md and premises_6648_q3_visible_two_positive_addendum.md |
| 1 | Remaining nested j=3,c≤1 and 2 or 3 near stars | site-team-08/6648_nested_single_tap_j3_c01.md |

In the final row the tapped M equals the visible literal OR its dirty donor and accepts both near singletons. Any ordinary top seeing it by an OR-only path must have x as opposite literal and hence must be A. Every lambda extension of M therefore feeds A and is equal to M unless the spare paid gate genuinely enlarges M downstream. An unaffected centreless output or one requiring either donor loses a batch as detailed in the source. If the genuine enlargement does occur, it aliases its remaining operand on H when the tapped donor is disabled, and its exceptional support disappears from every batch. A named paid raw reader either removes the ordinary correction or kills the remaining centreless output on that slice. The four-batch inequality used under three near stars is specifically F(1,4)≤6, from the four-internal-star argument in the visible index. The source's shorthand F(1,4) in that step refers to this stronger inequality. I independently checked the downstream alias, the direct-dirty-predecessor split, and the original-star guard transfer against the preceding proofs.

All F bounds use the same binary exceptional H support across all owners; H deletes 3,6,7. Restriction is used to count original marked edges, without assuming leastness after projection. The table is a mathematical proof map conditional on the cited base lemmas. It does not treat an entrance with a raw-empty other pin, three dirty-reading ORs, or an unclean A. The SHA256 manifest below pins the proof texts.
5aaae5b7722b812ce86754701271ff68f1dbdcd68c7f85a01a4af8f776a99559  premises_6648_q3_empty_repeated_donor.md
9706324af1ba2533a26a1aa43fe90c451e64a96f6215827f5b17fbb29d193072  premises_6648_q3_empty_c1_distinct_donors.md
5df2c6be167325e80b01e5ac79037e1ab48ea735ad248d0f589fd307408b2d2e  premises_6648_q3_empty_distinct_donors_all_c.md
b43ffdb8683507742ead77e08458d8a726de02e47de935b7e0a6042874394577  premises_6648_q3_two_direct_taps.md
6ef770128fd363905939d3dd8ef6a8fbe01ffbc36a889b88e4f9496f02eadb78  premises_6648_q3_full_S_zero_taps.md
e3233d4f76e57b2a6652935243bab5f8b0629cac17edcb49d92deaf332e6bbf4  premises_6648_q3_full_S_one_tap.md
856fbd31f80672ddc24353bc81ab93543d5ce888acc11751603610de1e45b59c  premises_6648_q3_visible_two_positive_index.md
579ebcaaa9b844a9fbb95bd8fbb6848055006e9bb46aa13fab01a4541946bddb  premises_6648_q3_visible_two_positive_addendum.md
5556760b4a146f01a4ff7763880d5a3f549ed60f72e8f79f7cdeedfdb0a83235  ../site-team-08/6648_nested_single_tap_j3_c01.md
