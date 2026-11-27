# Discovering a symmetric leaf section from raw quadratic coefficients

Let V be the binary input space and O the r-dimensional output space. From the polar tensor B alone solve for all linear maps Φ:O*→V satisfying

    v(B(x,Φu)) = u(B(x,Φv))   for all x∈V and u,v∈O*.

Trilinearity permits checking coordinate basis triples. This is a homogeneous linear system in nr unknown bits. Any genuine leaf embedding that symmetrizes all varying matrices on all V satisfies it. For each candidate test B(Φu,Φv)=0 and independence of the r linear forms Dᵢ(x)=eᵢ(B(x,Φeᵢ)). The implementation tests individual nullspace basis vectors first, then their other nonzero combinations. If every nonzero solution is valid, as on a promised space of good scalar multiples, the first test succeeds. Generally recognition takes polynomial work times at most 2^d for solution-space dimension d. A supplied trial limit makes failure inconclusive.

Write H(x) for the matrix with columns B(x,Φeᵢ). It is symmetric for every x. For any w with Φw=0 one has H(x)w=0, whence wᵀH(x)w=w·D(x)=0 identically. Surjectivity of D implies w=0. Thus Φ embeds the leaf space L. Isotropy gives D(L)=0. Solve D(cⱼ)=eⱼ and let C be the span of these controls. It is disjoint from L; any further complement to C+L can be held at zero. This proves the necessary dimension test dim V≥2r without assuming that ker D equals L.

On controls c(t)=Σ cⱼtⱼ the varying leaf matrix H(c(t)) is symmetric with diagonal t. The remaining constant leaf matrix has columns F(Φeᵢ)+F(0) and may be arbitrary since leaf isotropy makes the leaf restriction affine. The binary parity proof in symmetric-overlap.md gives an odd number of t with invertible total leaf matrix. For the requested raw target T enumerate at most 2^r centers, subtract F(c(t)), solve for the leaves, and evaluate F on the raw witness. A missing section is not evidence of infeasibility.

The regression independently generates translated, input- and output-recoded examples with nonlocal symmetric off-diagonals, dense binary drift, pure-control quadratics, and an excess input. Across three fixtures (r=3,4,5) all 56 targets are checked by the planting evaluator. Their linear symmetry solution spaces have dimensions 5,4,1. Controls include a zero polar at adequate dimension and the insufficient-dimensional polar of a P₃.
