import ThresholdPublicThird
import ThresholdSharpGrowth
namespace ThresholdSharpGlobalLower
open ThresholdThirdDeletion ThresholdPublicMinimum
noncomputable def coeff : ℝ := 9765625/2048
theorem coeff_eq : coeff=(5/4:ℝ)^10*2^9 := by norm_num [coeff]

def RegularLower : Prop := ∀ B : ℝ, 0<B → ∀ ε : ℝ, 0<ε → ε≤1/2 →
  ∃ N : ℕ, ∀ m : ℕ, N≤m → RegularOrder m → 0≤surplus m → (surplus m)^10≤B*(m:ℝ)^3 →
    (1-ε)*coeff*(m:ℝ)^3≤(surplus m)^10

theorem unrestricted_lower (regular : RegularLower) (δ : ℝ) (pos : 0<δ) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → 0≤surplus n ∧
      (coeff-δ)*(n:ℝ)^3≤(surplus n)^10 := by
  have kp : 0<coeff := by norm_num [coeff]
  let ε := min (1/2:ℝ) (δ/(4*coeff))
  have ep : 0<ε := lt_min (by norm_num) (div_pos pos (by positivity))
  have eh : ε≤1/2 := min_le_left _ _
  have de : 4*coeff*ε≤δ := by
    have h := (le_div_iff₀ (show 0<4*coeff by positivity)).mp
      (min_le_right (1/2:ℝ) (δ/(4*coeff)))
    change 4*coeff*min (1/2:ℝ) (δ/(4*coeff))≤δ
    linarith
  obtain ⟨R,reg⟩ := regular (8*coeff) (by positivity) ε ep eh
  obtain ⟨k,hk⟩ := exists_nat_ge (max coeff (18/ε^2))
  let N := max (2*R+2^404) (k+128)
  refine ⟨N,?_⟩
  intro n large
  have big : 2*R+2^404≤n := (le_max_left _ _).trans large
  have kn : k+128≤n := (le_max_right _ _).trans large
  have K : (k:ℝ)≤(n:ℝ) := by exact_mod_cast (show k≤n by omega)
  have x : (128:ℝ)≤n := by exact_mod_cast (show 128≤n by omega)
  have en := (ThresholdThirdDeletion.unrestricted ThresholdRegularThird.regular (by omega : 2^402≤n)).1
  refine ⟨en,?_⟩
  have xn : 0≤(n:ℝ)^3 := pow_nonneg (Nat.cast_nonneg _) _
  by_cases bounded : (surplus n)^10≤coeff*(n:ℝ)^3
  · have epsCut : 18≤ε^2*(n:ℝ) := by
      have d := (div_le_iff₀ (sq_pos_of_pos ep)).mp
        (((le_max_right coeff (18/ε^2)).trans hk).trans K)
      linarith
    have cut : coeff≤(n:ℝ)^2 := by
      have h := ((le_max_left coeff (18/ε^2)).trans hk).trans K
      nlinarith [mul_nonneg (show 0≤(n:ℝ) by positivity) (show 0≤(n:ℝ)-1 by linarith)]
    obtain ⟨m,lo,hi,kind,_,_,ratio,order⟩ :=
      ThresholdSharpGrowth.terminal_close (by omega : 128≤n) ep epsCut cut bounded
    have half : (n:ℝ)≤2*(m:ℝ) := by
      nlinarith [mul_nonneg (show 0≤1/2-ε by linarith) (Nat.cast_nonneg n (α:=ℝ))]
    have H : n≤2*m := by exact_mod_cast half
    have em := (ThresholdThirdDeletion.unrestricted ThresholdRegularThird.regular (by omega : 2^402≤m)).1
    have ypow := pow_le_pow_left₀ em order 10
    have ncube := pow_le_pow_left₀ (Nat.cast_nonneg n (α:=ℝ)) half 3
    have boundM : (surplus m)^10≤8*coeff*(m:ℝ)^3 := by
      nlinarith only [ypow,bounded,mul_le_mul_of_nonneg_left ncube kp.le]
    have core := reg m (by omega) kind em boundM
    have one : 0≤1-ε := by linarith
    have rcube := pow_le_pow_left₀ (mul_nonneg one (Nat.cast_nonneg n)) ratio 3
    have applied := mul_le_mul_of_nonneg_left rcube (mul_nonneg one kp.le)
    have bern : 1-4*ε≤(1-ε)^4 := by
      nlinarith [mul_nonneg (sq_nonneg ε) (show 0≤6-4*ε+ε^2 by nlinarith [sq_nonneg ε])]
    have small : coeff-δ≤(1-ε)^4*coeff := by
      nlinarith only [de,mul_le_mul_of_nonneg_right bern kp.le]
    nlinarith only [core,ypow,applied,mul_le_mul_of_nonneg_right small xn]
  · have lower := lt_of_not_ge bounded
    nlinarith only [lower,mul_nonneg pos.le xn]

theorem rational_endpoint (regular : RegularLower) (ε : ℝ) (ep : 0<ε) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → 0≤surplus n ∧
      (9765625-ε)*(n:ℝ)^3≤2048*(surplus n)^10 := by
  obtain ⟨N,h⟩ := unrestricted_lower regular (ε/2048) (by positivity)
  refine ⟨N,fun n large => ?_⟩
  obtain ⟨pos,ineq⟩ := h n large
  unfold coeff at ineq
  exact ⟨pos,by linarith only [ineq]⟩

#print axioms rational_endpoint
end ThresholdSharpGlobalLower
