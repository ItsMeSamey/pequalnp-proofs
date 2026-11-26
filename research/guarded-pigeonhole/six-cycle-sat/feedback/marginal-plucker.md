# Two protected landmark marginals

Assume every physical switch mask has k≥2 trajectories, with exactly one named anchor on each. Let E=∏(1+h_g) enumerate every mask, X_i and Y_i enumerate masks where root a or root b respectively occupies class i, and Z_ij enumerate masks whose two distinct root classes are i,j in either order. A mask has monomial ∏_{g on}h_g in every polynomial.

Use one common interlacement chart. Introduce an isolated dummy orbit with transposition spokes to the k anchors and both roots. Place each spoke off in the reference. At coincident marks separate the cut points by passive subdivisions. To obtain one reference tour across multiple untied components, join their reference cycles and the dummy by a tree of extra reference-only transpositions. These connector indices are mandatory in every evaluated section. All physical gates use the same tag convention in every section. With k spokes active, one orbit results precisely when their original marks lie on k different trajectories: every one of the k transpositions must merge an orbit into the dummy. With k−2 spokes there are always at least three orbits.

For distinct i,j take as common part the section with the k−2 other anchor spokes. Adjoin marked spoke indices a,b,z_i,z_j. The four-index Pfaffian identity gives the Pfaffian of the common part times that of the all-four section as the sum of the three products of complementary two-index sections. This follows by Schur complementation of a generic invertible alternating common block and polynomial specialization. The common block has even size since its addition of two indices can yield the nonzero envelope. Its Pfaffian is identically zero by the k−2 bound. Thus over the polynomial ring of characteristic two,

    E Z_ij = X_i Y_j + X_j Y_i.

These are ordinary products; all exponents including two are retained. A common orientation reversal of a physical bit acts by h_g times reciprocal substitution in that variable on every multilinear mask polynomial, hence preserves the homogeneous quadratic identity. Alternatively use the canonical physical edge weights from two-cycle-promise.md, scaling also every incidence to a potential spoke.

Let M be the all-anchor alternating section, with Pf M=E, invertible over the rational function field. For root a let v denote the root-spoke column to the indices of M, with the same gate weights. Replace the mandatory row and column z_i by that spoke. Pfaffian expansion at the replaced index and the Pfaffian cofactor formula give

    X_i/E = vᵀ M⁻¹ e_{z_i}.

The entry v at z_i does not matter: an alternating inverse has zero diagonal. The analogous probe for root b yields Y_i/E. Keeping z_i and appending the root would have different orbit semantics. In a common raw-tag chart all spoke incidences are constant. If physical bit conventions differ from raw ones, use the same reversals on every polynomial before interpreting masks. Ratios cancel the common reversing monomial; clear denominators before specializing.

With physical tags set h_g=t_g/(1+t_g) and divide each marginal by E. Each mask then has weight ∏_{g on}t_g ∏_{g off}(1+t_g), giving its exact Boolean-mask indicator at each Boolean t after polynomial cancellation. Equivalently, in the raw chart translate h_g by one, set t_g=1/h_g, and account for the resulting per-gate bit convention: raw absent has normalized weight t_g and raw present has weight 1+t_g. Thus at t_g=0 the raw bit is present. Apply the chart's fixed bit reversal to obtain the physical switch mask.

The joined-mask polynomial J obeys J=E+Σ_{i<j} Z_ij. Since Σ X_i=Σ Y_i=E, summation of the four-index identities gives E J=Σ_i X_i Y_i. Given a suitable identity test one may force physical bit 0 or 1 by using indicator gate weights and updating E; keep a branch whose joined polynomial remains nonzero. In normalized Boolean coordinates J/E is multilinear, so restricting one coordinate to 0 and 1 likewise suffices. Trace the final decoded mask on the original network. These identities alone give no generic deterministic identity test for the resulting sum.

The [checker](check_marginal_plucker.py) traces every mask on each of 180 seeded protected networks. It compares every ordinary polynomial coefficient for all 294 unordered class pairs by encoding exponents in base three. In 82 networks the ordered pair of root classes varied with the mask. The inverse formula is proved by cofactors; this checker verifies the product identity.
