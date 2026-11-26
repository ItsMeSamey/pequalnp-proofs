import ThresholdPublicShared
import ThresholdPublicMinimum
import ThresholdThirdPower
import Mathlib.Analysis.Real.Sqrt

namespace ThresholdThirdDeletion
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity T2SoleOrSplice
open ResidualSurplus T2CubeDeletion T2RegularOrDelete ThresholdPublicMinimum

def RegularOrder (m : ℕ) : Prop :=
  ∃ gs : List Raw, ∃ out, Nonempty (LexMinimum m (source gs out)) ∧ Regular m gs

theorem terminal (n : ℕ) (hn : 2≤n) : ∃ m, 2≤m ∧ m≤n ∧
    minimum m + 3*(n-m) ≤ minimum n ∧ (m=2 ∨ RegularOrder m) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases two : n=2
    · subst n; exact ⟨2,by decide,by omega,by simp,Or.inl rfl⟩
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
    obtain ⟨C,hm,hc,hs⟩ := attained (k+1)
    rcases ThresholdPublicShared.shared_or_delete (by omega : 2≤k) C hm hc with
      ⟨F,fm,fc,save⟩ | ⟨gs,out,M,reg,_⟩
    · obtain ⟨m,lo,hi,price,kind⟩ := ih k (by omega) (by omega)
      have cheapest := le_size fm fc
      refine ⟨m,lo,by omega,?_,kind⟩
      change minimum m + 3*((k+1)-m) ≤ minimum (k+1)
      omega
    · exact ⟨k+1,by omega,by omega,by simp,Or.inr ⟨gs,out,⟨M⟩,reg⟩⟩

noncomputable def surplus (n : ℕ) : ℝ :=
  (minimum n : ℝ) - 2*(n:ℝ) - Real.sqrt (2*(n:ℝ))
def RegularTenth : Prop := ∀ m : ℕ, (2:ℕ)^400≤m → RegularOrder m →
  0≤surplus m ∧ (m:ℝ)^3≤((2:ℝ)^14*surplus m)^10

theorem unrestricted (regular : RegularTenth) {n : ℕ} (large : (2:ℕ)^402≤n) :
    0≤surplus n ∧ (n:ℝ)^3≤((2:ℝ)^15*surplus n)^10 := by
  have hn : 2≤n := by omega
  obtain ⟨m,lo,hi,cost,kind⟩ := terminal n hn
  let x : ℝ := n
  let y : ℝ := m
  let t := Real.sqrt (2*x)
  let u := Real.sqrt (2*y)
  have X : (128:ℝ)≤x := by dsimp [x]; exact_mod_cast (show 128≤n by omega)
  have Y : (2:ℝ)≤y := by dsimp [y]; exact_mod_cast lo
  have LE : y≤x := by dsimp [x,y]; exact_mod_cast hi
  have T : 0≤t := Real.sqrt_nonneg _
  have U : 0≤u := Real.sqrt_nonneg _
  have TT : t^2=2*x := Real.sq_sqrt (by linarith)
  have UU : u^2=2*y := Real.sq_sqrt (by linarith)
  have price : (minimum m:ℝ)+3*(x-y)≤(minimum n:ℝ) := by
    dsimp [x,y]
    exact_mod_cast (show (minimum m:ℤ)+3*((n:ℤ)-(m:ℤ))≤(minimum n:ℤ) by
      have h : (minimum m:ℤ)+3*((n-m:ℕ):ℤ)≤(minimum n:ℤ) := by exact_mod_cast cost
      rwa [Nat.cast_sub hi] at h)
  by_cases small : 4*m<n
  · have S : 4*y≤x := by dsimp [x,y]; exact_mod_cast small.le
    have bound : t≤x/8 := by
      by_contra! bad
      nlinarith [mul_pos (show 0<t-x/8 by linarith) (show 0<t+x/8 by linarith),
        mul_nonneg (show 0≤x by linarith) (show 0≤x-128 by linarith)]
    have z : x≤8*surplus n := by
      change x≤8*((minimum n:ℝ)-2*x-t)
      linarith [Nat.cast_nonneg (minimum m) (α:=ℝ)]
    have non : 0≤surplus n := by linarith
    have stronger : x≤(2:ℝ)^15*surplus n := by norm_num; linarith
    have smallpow : x^3≤x^10 := pow_le_pow_right₀ (by linarith : 1≤x) (by decide : 3≤10)
    exact ⟨non,smallpow.trans (pow_le_pow_left₀ (by linarith) stronger 10)⟩
  · have hbig : (2:ℕ)^400≤m := by omega
    have rr := regular m hbig (kind.resolve_left (by omega))
    have gap : t-u≤x-y := by
      have ut : 2≤u := by
        by_contra! bad
        nlinarith [mul_pos (show 0<2-u by linarith) (show 0<2+u by linarith)]
      have a : (t+u)*(t-u)=2*(x-y) := by nlinarith
      have b := mul_le_mul_of_nonneg_right (show 2≤t+u by linarith) (sub_nonneg.mpr LE)
      have c : (t+u)*(t-u)≤(t+u)*(x-y) := by linarith
      exact (mul_le_mul_iff_right₀ (show 0<t+u by linarith)).mp c
    have inc : surplus m≤surplus n := by
      change (minimum m:ℝ)-2*y-u≤(minimum n:ℝ)-2*x-t
      linarith
    have diff : x≤4*y := by dsimp [x,y]; exact_mod_cast (Nat.le_of_not_gt small)
    have cube := pow_le_pow_left₀ (by linarith : 0≤x) diff 3
    have ten := pow_le_pow_left₀ rr.1 inc 10
    have regpow : y^3≤((2:ℝ)^14*surplus m)^10 := rr.2
    refine ⟨rr.1.trans inc,?_⟩
    change x^3≤((2:ℝ)^15*surplus n)^10
    nlinarith only [cube,ten,regpow,pow_nonneg rr.1 10]

#print axioms terminal
#print axioms unrestricted
end ThresholdThirdDeletion
