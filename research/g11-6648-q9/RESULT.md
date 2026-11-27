# G11 surplus at nine exceptional OR gates

Under the original issued L-meta-6648 least TopForm hypotheses, suppose q=9. Then U≤j+2c+9 and the issued balance U+|J|=|X|+j gives |X|≤2c+|J|+9 for every issued choice of the selected sets. This is a positive mathematical exclusion on the research fork.

Write s=16−U. The previously published zero- and one-star bounds handle s≤1. If the bound failed at s≥2, then j+2c≤6−s. Since j≥3, this leaves only c=0 and three possibilities: s=2 with j=3 or 4, and s=3 with j=3. The original size-21 hypothesis used below follows from the issued size bound and the previously established size-21 floor. All counts and star endpoints are those of the original circuit.

| Starred edge set | Junk count | Proof |
|---|---:|---|
| Two edges, either shape | 3 | Published q10 packet, RESULT.md, first assertion valid for every q |
| Two touching edges | 4 | q9-two-touching-stars-four-junk.md |
| Two disjoint edges | 4 | 6648-two-disjoint-stars-four-junk.md |
| Three connected edges | 3 | twin_6648_q9_three_connected_stars.md covers triangle, three-leaf star, and four-vertex path |
| Three edges on five vertices | 3 | twin_6648_q4_9_p3_k2.md covers the two-edge path plus a disjoint edge |
| Three disjoint edges | 3 | 6648-q9-three-matching-closure.md |

These are all shapes of a simple graph with two or three edges after ignoring isolates. No reader-type split is needed. For the last row use the short six-import exclusion in 6648-q9-three-matching-six-import-short.md, the final t=3 argument of 6648-q9-three-matching-saturation.md, and then the t=4,5 argument in the closure. The low-input AND floor mentioned in some sources is not required in this dispatch: the P3-plus-edge contradiction uses upper bounds on t only, and three disjoint edge groups already force three tops. The original graphs, existing certificates and source definitions remain in the prior deposits identified in PRIOR.md. The proof is source-level.
