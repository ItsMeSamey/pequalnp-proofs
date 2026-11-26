# Target-dependent quotient for exact named kernels

Write A:E→V and B:R→V for the binary ordinary and named column maps.
Fix the desired kernel K⊂R. Put W=B(K) and H=πA where π:V→V/W.
Use a primal lane for each basis k of K, a dual lane for each basis b of
K-perp, and disallow every cross overlap on E.

The primal lane must be a cycle c of H with the W-valued score Ac=Bk.
For a dual lane choose a linear section d↦f_d of W-perp→row H, the map
being f↦A^T f. Set Z=ann(im A+W). Require the linear score B^T f_d
to equal b modulo B^T Z. Both score maps on the cycle or cocycle
space are extendible to ambient edge labels by Gaussian elimination.

If a contraction set X and deletion of other ordinary columns yield K,
lift each k on X, giving Ac=Bk, and lift each b by a functional f
vanishing on A_X with B^T f=b. It annihilates W since b⊥K; A^T f is
therefore in row H. Conversely set X to the union of the primal
supports. The equations Ac=Bk put K inside the named minor kernel.
For each b choose z∈Z with B^T(f_d+z)=b. The functional f_d+z
annihilates A_X by physical disjointness, so K-perp lies in the
minor's cocycle space. These two inclusions force equality.

Test regularity of this one target-dependent H, computable before X.
If regular, the homogeneous portfolio algorithm gives deterministic XP
for fixed root count regardless of leader sizes. More generally a
strong regularity backdoor on H suffices: choosing delete or contract
at each backdoor element permits, respectively, only dual or only
primal activity. Transfer each lane's score by the usual linear minor
sections; at a loop or coloop enumerate the free active-family bits.
These choices cover all common physical partitions. The theorem does
not assert H is automatically regular from the regularity of A or of
any earlier reference D.
