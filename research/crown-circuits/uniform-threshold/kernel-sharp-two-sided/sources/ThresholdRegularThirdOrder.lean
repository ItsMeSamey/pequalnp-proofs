import ThresholdRegularThirdCore
import ThresholdThirdPublicPower
namespace ThresholdRegularThird
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ResidualSurplus ThresholdPublicMinimum
open T2SoleOrSplice T2RegularOrDelete T2CubeDeletion ThresholdThirdDeletion

def SmallRegularPower : Prop := ∀ {n out : Nat} {gs : List Raw}, 5≤n →
  LexMinimum n (source gs out) → Regular n gs → ∀ t E : ℝ, t^2=2*(n:ℝ) →
  (2:ℝ)^200≤t → E=1+max 0 (((source gs out).size:ℝ)-2*n-t) →
  E^5≤t^3 → t^3≤(2:ℝ)^65*E^5

set_option maxRecDepth 8192 in
theorem regular_order (smallPower : SmallRegularPower) : RegularTenth := by
  intro n large hreg
  obtain ⟨gs,out,⟨minim⟩,reg⟩ := hreg
  have hn : 5≤n := by omega
  let t := Real.sqrt (2*(n:ℝ))
  let z := surplus n
  let E := 1+max 0 z
  have sq : t^2=2*(n:ℝ) := Real.sq_sqrt (by positivity)
  have cut : (2:ℝ)^200≤t := by
    have low : (2:ℝ)^400≤(n:ℝ) := by exact_mod_cast large
    have pos : 0≤t := Real.sqrt_nonneg _
    have powEq : ((2:ℝ)^200)^2=(2:ℝ)^400 := (pow_mul (2:ℝ) 200 2).symm
    by_contra! bad
    have contra : t^2 < ((2:ℝ)^200)^2 := pow_lt_pow_left₀ bad pos (by decide)
    rw [sq,powEq] at contra
    exact (not_lt_of_ge (show (n:ℝ)≤2*n by rw [two_mul]; exact le_add_of_nonneg_right (Nat.cast_nonneg _))) (contra.trans_le low)
  have eq := lex_size (by omega : 2≤n) minim
  have ex : E=1+max 0 (((source gs out).size:ℝ)-2*n-t) := by rw [eq]; rfl
  have bound : t^3≤(2:ℝ)^65*E^5 := by
    by_cases small : E^5≤t^3
    · exact smallPower hn minim reg t E sq cut ex small
    · have pos : 0≤E := by dsimp [E]; linarith [le_max_left 0 z]
      have scale := mul_le_mul_of_nonneg_right (show (1:ℝ)≤2^65 by norm_num) (pow_nonneg pos 5)
      linarith
  exact ThresholdThirdPower.regular_tenth t n z E (by positivity) cut sq rfl bound
end ThresholdRegularThird
