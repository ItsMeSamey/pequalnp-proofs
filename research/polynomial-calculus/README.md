# A marked Boolean system of exact polynomial-calculus refutation degree four

Over the field with two elements, consider one equation per pivot and one parity marker:

    x_i ((Mx)_i + b_i) = 0        for 0 ≤ i < n
    ℓ·x + 1 = 0

There is a 22-variable unsatisfiable instance whose polynomial-calculus refutation degree is exactly four. There is also a satisfiable 12-variable instance with an affine consequence that requires degree four. Simultaneous cancellation of quartic terms across different variable multiplications succeeds on both underlying targets.

## Calculus and conventions

A polynomial is in squarefree normal form in the Boolean quotient, so x_i² = x_i. A PC derivation starts with the input polynomial equations, represented by their left sides; its rules are addition over GF(2) and multiplication by a single variable. We certify the degree-three lower bound even if a cubic line may be multiplied whenever its squarefree product remains cubic. For the degree-four upper bound, every multiplication in the recorded proof starts from a line of degree at most three. Consequently the same degree bounds hold in ordinary unreduced PC over GF(2) with Boolean axioms x_i²+x_i=0. Projection into squarefree form carries every degree-three proof into the checked lower-bound calculus. Conversely the degree-four trace lifts by using multiples of the Boolean axioms to reduce any repeated variable in a product of degree at most four.

## The base and the instances

The base uses eleven coordinates numbered 0 through 10. A mask m denotes the set of indices j whose jth least-significant bit equals one. The entries below are the eleven row masks in index order.

    M = [258,132,8,144,544,1,9,1088,128,256,512]
    b = 1892

Every base model satisfies x₁₀=0. To see this without enumeration, begin with six pivots on a directed cycle, row i selecting coordinate i+1 modulo six, and offsets all one. A selected vertex forces its successor, so all six coordinates are equal and x₀+x₃ always vanishes. Given an unmarked base with homogeneous invariant ℓ·x=0, append a new pivot t. Select a column c, append it to the old matrix on the right, change the old offsets to b+c, and append the row ℓ with its new column entry zero and offset one. If t=1, the old rows become precisely the old system and the new row requires ℓ·x=1. Thus t is forced zero. Taking t as the new invariant at each step, use column masks 0, 10, 1, 16 and 128 in order. The result is the displayed base. The checker reconstructs its masks and enumerates exactly 38 base models.

**Satisfiable instance.** Append an unconstrained twelfth pivot with zero row and offset, and set the marker to x₁₁=1. It has 38 models and entails x₁₀=0. A degree-three derivation of x₁₀ would specialize at x₁₁=1 to such a derivation on the base: the new axioms become zero, and multiplication by the pinned variable becomes the identity. The base certificate excludes the latter derivation.

**Unsatisfiable instance.** Use two disjoint copies of the base, so the combined matrix is block diagonal with identical blocks M. The offset is 1892 + 2¹¹·1892. Add the marker x₁₀+x₂₁=1. Each copy forces its marked bit to zero. The doubled lower-bound certificate excludes derivation of the constant one in degree three.

## Verification and upper bound

Run from any directory using Python 3 without optimization; the scripts use only the standard library.

    python /workspace/scratch/pc-release/check_certificate.py
    python /workspace/scratch/pc-release/independent_audit.py
    python /workspace/scratch/pc-release/degree_falls.py

The two lower-bound JSON files contain the matrix, offset, marker and a GF(2) vector-space basis. Each basis polynomial is an array of monomial masks (0 denotes the constant monomial). In affine-base.json the certified space W has dimension 170, contains every base axiom and excludes x₁₀. In unsat-marker.json W has dimension 1,252, contains all 23 doubled axioms and excludes one. For each variable the checker forms the full linear image x_i W in degree at most four. A degree-ordered echelon basis of that image has low-pivot rows spanning its intersection with degree at most three. Each such row is verified to lie in W. By induction every degree-three PC line lies in W. This certificate requires only that W is closed and contains the axioms.

The separate audit independently rebuilds the *least* closed spaces from the input axioms and checks equality with the certificates. Its rank sequences are 11, 110, 148, 170 on the base and 23, 484, 848, 1020, 1252 on the doubled instance.

In degree4-proof.json, each entry is one derivation line. The instruction ["a",i] takes axiom i, ["+",j,k] adds earlier lines j and k, and ["*",j,i] multiplies line j by variable i. The checker replays all 155 lines and checks the final polynomial is x₁₀. In the doubled system use the same derivation once in each block and add the two forced bits to the marker to obtain one. This proves exact degree four for both targets.

## Simultaneous degree falls

For d=3 let V_d be the squarefree polynomials of degree at most d. The stronger procedure starts with the axiom span W in V_d, then iterates

    W ← (W + x₀W + ⋯ + xₙ₋₁W) ∩ V_d.

The sum takes place in V₄. Quartic coefficients may cancel across products by different variables *before* the degree cap is applied. degree_falls.py implements that rule by building a single echelon basis of the entire sum and retaining its low pivots. It obtains the following dimensions, starting from the axiom span.

| Input | Successive dimensions | Target |
|---|---|---|
| Base | 11, 110, 158, 194 | Derives x₁₀ |
| Doubled | 23, 484, 868, 1120, 1566, 1788, 1794 | Derives one |

The doubled terminal space is the entire 1,794-dimensional cubic space. This outcome can also be deduced from the degree-four trace. With axioms in V₃, the simultaneous fixed point gives exactly the V₃ consequences of squarefree PC allowing retained quartic lines but restricting multiplication to source lines in V₃. Every simultaneous sum is a legal sequence of such degree-four operations. Conversely, let W be the simultaneous fixed point and H = W + Σ_i x_iW. A degree-four derivation using those multiplication rules stays in H: addition stays there, and every line that can be multiplied belongs to H ∩ V₃ = W. This equivalence uses the indicated restriction on multiplication sources. The example distinguishes ordinary degree-three inference from the simultaneous rule and leaves higher asymptotic degree bounds open.

The [prefix-circulation theorem](prefix-circulations.md) gives an integral projection of the unmarked mask LP and a one-round affine export for every parity marker when the supplied potential criterion holds.
