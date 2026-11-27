# Every seven-term representation of the CCZ cube shares a signed Pauli

Use the fidelity and Gram bounds of few-products-must-share.md, SHA256 ae93b4f220ab0561127637039cb4fb7c5714fc79ba61971c5f5e64c62671f195, including its constants h=225/2048, m=25/256, u=49/512, o=9/100 and l=405/4096. Assume there is no shared signed nonidentity Pauli. Call a block-product atom large if all three factors belong to H or M. Every other block-product atom has squared fidelity at most l. A small product with all H factors ruled out has fidelity at most (5/16)(1/2)^2<o. Ordinary and exceptional below refer to block product and nonproduct as in the cited proof.

There are at most two large products. Indeed if two exist their factors at any one position form either H/M with the H point on the M plane or complementary M/M. In each case a third H or M at this position would share a signed local Pauli with at least one of the two. Thus if two exist, every further product has all three factors outside H,M and fidelity at most (5/16)^3<o. No H- or M-type Bell can occur and the cited two-large argument rules out a GHZ with all-H branch. Hence the total fidelity is at most (9/16)^3+1/8+5o<0.7530.

If no large product exists, all small products cost at most l, which exceeds m, and only the at most three H-type Bells can exceed l. The total is bounded by 3h+4l<0.726.

For one large product consider its types:
- MMM costs 1/8. The rest cost at most 3h+3l, giving a total below 0.752.
- HMM costs (9/16)/4, and allows at most two H-type Bells. At zero or one the total is at most (9/16)/4+h+5l<0.746. At two, their spectators occupy the two M positions. Between them and the H position of the product, none of the remaining ordinary factors can be H at any position. Thus every small product costs less than o and the total is at most (9/16)/4+2h+4m<0.752.
- HHM costs (9/16)^2/2. With no H-type Bell its total is at most (9/16)^2/2+6l<0.752. With one H-type Bell at the M site all H positions have again been blocked, so small products cost less than o. At most two M-type Bells occur by the earlier plane-incidence count, giving the upper bound (9/16)^2/2+h+2m+3u<0.752.
- HHH forbids H in every other ordinary product and every Bell spectator. There are at most three M-type Bells and every nonproduct outside these costs ≤o, by the all-H branch exclusion. The total is at most (9/16)^3+3m+3o<0.742.

All possibilities fall below the necessary Gram threshold 0.7538. Thus some pair shares a signed nonidentity Pauli. This forces a common Pauli eigenvalue but does not decide if the list exists or if any third atom shares that eigenvalue.
