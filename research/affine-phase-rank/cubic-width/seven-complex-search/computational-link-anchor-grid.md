# Six-qubit anchor grid for IZZ, ZZZ, IZJ and IZR

Choose an active computational block Y and write the signed global Pauli as Z_Y Q, taking Z_Y on a single control bit s and Q on the two remaining parties. Use target-preserving affine coordinates with data p∈F₂² and raw target phase γ(s,p)=(−1)^(s p₁p₂). Absorb the global Pauli sign into Q. The sector label δ is ±1. All statements allow repeated or dependent branch entries, arbitrary complex weights and either sign.

For any ordered p₀,p₁∈F₂² take the raw two-point stabilizer bra on Y with values γ(s,p_s) at (s,p_s). It sends each projected target Π_δ G₃ exactly to G₂: at sign s the scaled target fiber is the projection of G₂ onto the Q eigenvalue δ(−1)^s, and the two add to G₂. Thus each of the sixteen cells in each sign requires at least four surviving branch atoms. In a five-survivor branch the two local computational supports of every pair of branch rays cover an entire parity plane between them on at least one of the two sides. Otherwise choose a missing point on each side to kill both, leaving at most three. Here survival of a cell is exactly presence on at least one selected point since its two remote fibers have orthogonal Q eigenvalues. In a four-survivor branch each individual ray must cover an entire local plane on at least one side.

For any δ-sector ray φ use
[
 B_δ(p₀,p₁)=γ(0,p₀) φ(0,p₀)+γ(1,p₁) φ(1,p₁)
]
with six-qubit vector fibers. The sixteen cell equations with the original shared coefficients reconstruct the entire projected branch: project onto the relevant Q sign to isolate either raw fiber and undo the sign γ. Even four pairs forming a perfect matching between the two planes suffice. The arrays satisfy the componentwise additive rectangle relations B(a,b)+B(c,d)=B(a,d)+B(c,b). Each nonzero cell is a stabilizer ray by contraction. One fixed remote Clifford diagonalizing Q makes the two summands disjoint in computational coordinates; raw column gauges can then be chosen consistently from the full physical column rather than normalized anew in each cell.

A mixed parent's opposite sign rays differ by a signed original Pauli tensor, including its single fixed fourth-root phase in raw gauges. Write its Y part up to that phase as X^(e,d) Z^b, with e acting on the control and d on the data. Let T be its two-party Pauli part. For a positive cell p_s the negative source has control t=s⊕e and data q_t=p_s⊕d. Thus the common permutation of the sixteen grid positions for this parent is translation in both data arguments by d, plus swapping the two arguments when e=1. On each of the source cell's two orthogonal Q fibers the extra relative sign, besides the single parent phase and T, is
[
 r_s=γ(s,p_s)γ(t,q_t)(−1)^{b·(t,q_t)}.
]
This follows by applying the raw Pauli to the source fiber before its positive contraction. The pair r₀,r₁ acts on the source Q eigenspaces by ±I or ±Q, so the remote partner is a Pauli translate with this determined sign correction on every cell. Zero fibers and zeros of entire cells follow the same permutation. These identities use the same parent weight throughout and can be verified before canonicalizing rays, including both parities of e and repeated ray directions. They give explicit cross-cell constraints beyond separate G₂ rank checks. They do not assert that independently meeting the counts supplies physical parents.
