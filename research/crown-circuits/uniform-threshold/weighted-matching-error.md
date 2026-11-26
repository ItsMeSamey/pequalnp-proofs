# A weighted four-cycle count for the sharp coefficient

Let b=(5/4)2^(9/10). For the unrestricted minimum circuit size for monotone threshold two,

    2n+√(2n)+b n^(3/10)−O(n^(1/5)) ≤ C(n)
      ≤ 2n+√(2n)+b n^(3/10)+O(n^(7/30)).

Use the explicit trimming in `sharp-receiver-error.md`, with E=Θ(h^(3/5)), g'=h−O(h^(4/5)), z=L/(hE), and w≤(1−z)E+O(E h^(−1/5)). Let Λ be the sum over four-sets of max(b₄−1,0), where b₄ counts the perfect matchings on that four-set. The restricted cold-pair count has already shown Λ≤L+O(h^(7/5)).

For i<j in the effective receiver graph set γ_ij=2/3 if ij is an edge and 1 otherwise. Write c_ij for the codegree of i,j and T=Σc_ij. Then

    Λ ≥ (1/2) Σ γ_ij binom(c_ij,2).

Indeed a codegree term is a four-cycle with a chosen opposite pair. On a four-set with fewer than two perfect matchings there are no such terms. A four-set with two perfect matchings contains one four-cycle, giving at most two units before halving. If all three perfect matchings occur the four-set is complete, so the six weighted terms give exactly four units before halving. These are all cases.

By weighted Cauchy–Schwarz and γ_ij≤1,

    Λ ≥ (1/4) (T²/(binom(w,2)+g'/2)−T).

Here Σγ_ij^(−1)=binom(w,2)+g'/2. The crude four-cycle estimate, g'∼h, and ordinary codegree Cauchy already imply w=Ω(h^(3/5)): since w=O(h^(3/5)), C4=Ω(h⁴/w⁴) while C4=O(hE). In particular g'/w²=O(h^(−1/5)). Also T≥2g'²/w−g' and T=O(h^(7/5)). Consequently

    L+O(h^(7/5)) ≥ (2−O(h^(−1/5)))h⁴/w⁴.

The remaining error terms in `sharp-receiver-error.md` are all O(h^(−1/5)) relative, including the bounded-derivative optimization on 0≤z≤1+O(h^(−1/5)). Hence E≥(5/4)2^(3/5)h^(3/5)−O(h^(2/5)). As before h=t+O(E) for t=√(2n), and the three-gate deletion alternative transfers the regular bound to all large n. This yields the stated lower bound; the upper bound is `short-signatures.md`.
