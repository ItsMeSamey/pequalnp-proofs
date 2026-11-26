import ThresholdThirdDeletion
import ThresholdPublicFourThirds
namespace ThresholdSharpTerminalRatio
open ThresholdThirdDeletion ThresholdPublicMinimum

/-- Bounded normalized third-order surplus eventually lies below the leading square root.
The coefficient A bounds the tenth power of the normalized surplus. -/
theorem bounded_to_sqrt {x z A : ℝ} (hx : 1≤x) (large : A≤x^2)
    (upper : z^10≤A*x^3) : z≤Real.sqrt (2*x) := by
  let t := Real.sqrt (2*x)
  have tn : 0≤t := Real.sqrt_nonneg _
  have ts : t^2=2*x := Real.sq_sqrt (by linarith)
  have fifth : t^10=(2*x)^5 := by calc
    t^10=(t^2)^5 := by ring
    _=_ := by rw [ts]
  have Aupper := mul_le_mul_of_nonneg_right large (pow_nonneg (by linarith : 0≤x) 3)
  by_contra! bad
  change t<z at bad
  have more := pow_lt_pow_left₀ bad tn (by decide : (10:ℕ)≠0)
  nlinarith only [fifth,upper,Aupper,more,pow_nonneg (by linarith : 0≤x) 5]

/-- Explicit epsilon bound on a single regular terminal of the actual deletion chain. -/
theorem ratio {n : ℕ} (large : 128≤n) {ε : ℝ} (ep : 0<ε)
    (epsCut : 18≤ε^2*(n:ℝ))
    (upper : surplus n≤Real.sqrt (2*(n:ℝ))) :
    ∃ m : ℕ, 2≤m ∧ m≤n ∧ RegularOrder m ∧
      minimum m+3*(n-m)≤minimum n ∧
      (n:ℝ)-(m:ℝ)≤3*Real.sqrt (2*(n:ℝ)) ∧
      (1-ε)*(n:ℝ)≤(m:ℝ) ∧ surplus m≤surplus n := by
  obtain ⟨m,lo,hi,price,kind⟩ := terminal n (by omega)
  obtain ⟨C,mono,computes,eq⟩ := attained m
  have lower := ThresholdPublicFourThirds.native_real lo C mono computes
  rw [eq] at lower
  let x : ℝ := n
  let y : ℝ := m
  let t := Real.sqrt (2*x)
  let u := Real.sqrt (2*y)
  have X : 128≤x := by dsimp [x]; exact_mod_cast large
  have Y : 2≤y := by dsimp [y]; exact_mod_cast lo
  have LE : y≤x := by dsimp [x,y]; exact_mod_cast hi
  have T : 0≤t := Real.sqrt_nonneg _
  have U : 0≤u := Real.sqrt_nonneg _
  have TT : t^2=2*x := Real.sq_sqrt (by linarith)
  have UU : u^2=2*y := Real.sq_sqrt (by linarith)
  have priceR : (minimum m:ℝ)+3*(x-y)≤(minimum n:ℝ) := by
    dsimp [x,y]
    exact_mod_cast (show (minimum m:ℤ)+3*((n:ℤ)-(m:ℤ))≤(minimum n:ℤ) by
      have h : (minimum m:ℤ)+3*((n-m:ℕ):ℤ)≤(minimum n:ℤ) := by exact_mod_cast price
      rwa [Nat.cast_sub hi] at h)
  change (minimum n:ℝ)-2*x-t≤t at upper
  have ly : 2*y-6≤(minimum m:ℝ) := by
    dsimp [y]; linarith [Real.sqrt_nonneg ((m:ℝ)+3)]
  have six : 6≤t := by
    by_contra! bad
    nlinarith [mul_pos (show 0<6-t by linarith) (show 0<6+t by linarith)]
  have delta : x-y≤3*t := by linarith
  have half : 3*t≤x/2 := by
    by_contra! bad
    nlinarith [mul_pos (show 0<3*t-x/2 by linarith) (show 0<3*t+x/2 by linarith),
      mul_nonneg (show 0≤x by linarith) (show 0≤x-72 by linarith)]
  have notBase : m≠2 := by
    intro zz
    have yy : y=2 := by dsimp [y]; rw [zz]; norm_num
    linarith
  have epsBound : 3*t≤ε*x := by
    change 18≤ε^2*x at epsCut
    have sq := mul_le_mul_of_nonneg_right epsCut (show 0≤x by linarith)
    by_contra! bad
    nlinarith [mul_pos (show 0<3*t-ε*x by linarith)
      (show 0<3*t+ε*x by nlinarith [mul_pos ep (show 0<x by linarith)])]
  have ut : 2≤u := by
    by_contra! bad
    nlinarith [mul_pos (show 0<2-u by linarith) (show 0<2+u by linarith)]
  have gap : t-u≤x-y := by
    apply (mul_le_mul_iff_right₀ (show 0<t+u by linarith)).mp
    have b := mul_le_mul_of_nonneg_right (show 2≤t+u by linarith) (sub_nonneg.mpr LE)
    nlinarith
  refine ⟨m,lo,hi,kind.resolve_left notBase,price,delta,?_,?_⟩
  · change (1-ε)*x≤y
    linarith
  · change (minimum m:ℝ)-2*y-u≤(minimum n:ℝ)-2*x-t
    linarith

#print axioms bounded_to_sqrt
#print axioms ratio
end ThresholdSharpTerminalRatio
