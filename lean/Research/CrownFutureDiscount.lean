import Research.CrownTightCrossing

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge TightStep

theorem flags_concat (pre post : List Gate) (w : List Bool) :
    trueOrFlags (pre++post) w = trueOrFlags pre w ++ trueOrFlags post ((Circuit.mk pre 0).wires w) := by
  induction pre generalizing w with
  | nil => rfl
  | cons g pre ih =>
    change _ :: trueOrFlags (pre++post) (advance g w) = _ :: _
    rw [ih];rfl

theorem prefix_weight_factor {n : ℕ} (pre post : List Gate) (i : Fin n) :
    singletonWeight (Circuit.mk (pre++post) 0) i =
      singletonWeight (Circuit.mk pre 0) i *
      (1/2:ℚ)^((trueOrFlags post ((Circuit.mk pre 0).wires (singleInput i))).count true) := by
  unfold singletonWeight
  rw [flags_concat,List.count_append,pow_add]

/-- If the suffix charges each singleton in B at least once, an earlier
cold wire's support can count its overlap with B twice at final weights. -/
theorem future_discount_overlap (n : ℕ) (pre post : List Gate) (hm : Monotone2 (Circuit.mk pre 0))
    (a : ℕ) (cold : ((Circuit.mk pre 0).wires (List.replicate n false)).getD a false = false)
    (B : Finset (Fin n)) (later : ∀ i ∈ B,
      0 < (trueOrFlags post ((Circuit.mk pre 0).wires (singleInput i))).count true) :
    overlapMass (singletonWeight (Circuit.mk (pre++post) 0)) (wireSupport (n:=n) pre a) B ≤ 1 := by
  let H := wireSupport (n:=n) pre a
  let w := singletonWeight (n:=n) (Circuit.mk (pre++post) 0)
  let old := singletonWeight (n:=n) (Circuit.mk pre 0)
  have inter : H ∩ B = H.filter (· ∈ B) := by ext; simp
  change overlapMass w H B ≤ 1
  rw [overlapMass,inter,Finset.sum_filter,←Finset.sum_add_distrib]
  apply le_trans _ (singleton_weight_capacity (Circuit.mk pre 0) hm a cold)
  apply Finset.sum_le_sum
  intro i _
  let k := (trueOrFlags post ((Circuit.mk pre 0).wires (singleInput i))).count true
  have factor : w i = old i * (1/2:ℚ)^k := prefix_weight_factor pre post i
  have bound (j : ℕ) : (1/2:ℚ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have pos := weight_positive pre i
  change 0 < old i at pos
  by_cases ib : i ∈ B
  · rw [ite_eq_left ib,factor]
    have hk : 0 < k := later i ib
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [hj,pow_succ]
    nlinarith [mul_nonneg pos.le (sub_nonneg.mpr (bound j))]
  · rw [ite_eq_right ib,add_zero,factor]
    simpa using mul_le_mul_of_nonneg_left (bound k) pos.le
end PEqualNP.Research.MissingCell
