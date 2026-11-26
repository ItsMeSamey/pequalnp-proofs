import PEqualNP.Defs

namespace CrownWeightedCover
open scoped BigOperators

private theorem crossed (a b c d : ℕ) (hab : 4 ≤ a*b) (hcd : 4 ≤ c*d) :
    8 ≤ a*d+c*b := by
  have hp : 16 ≤ (a*d)*(c*b) := by
    calc 16 = 4*4 := rfl
         _ ≤ (a*b)*(c*d) := Nat.mul_le_mul hab hcd
         _ = _ := by ring
  by_contra! h
  have hs : (a*d+c*b)^2 ≤ 7^2 := Nat.pow_le_pow_left (by omega) 2
  have sq := sq_nonneg ((a*d : ℤ) - c*b)
  zify at hp hs
  nlinarith

/-- A weighted rectangle cover bound. The coordinate weights are scaled by four.
A binary OR-tree application supplies the two block capacities by Kraft's inequality. -/
theorem crown_weighted_cover {n k : ℕ} (A B : Fin k → Finset (Fin n)) (r c : Fin n → ℕ)
    (localBudget : ∀ i, 4 ≤ r i * c i)
    (rowCap : ∀ t, ∑ i ∈ A t, r i ≤ 4)
    (colCap : ∀ t, ∑ j ∈ B t, c j ≤ 4)
    (cover : ∀ i j : Fin n, i ≠ j → ∃ t, i ∈ A t ∧ j ∈ B t) :
    n*(n-1) ≤ 4*k := by
  classical
  let f (i j : Fin n) := if i ≠ j then r i*c j else 0
  let cell (i j : Fin n) (t : Fin k) := if i ∈ A t ∧ j ∈ B t then r i*c j else 0
  have once (i j : Fin n) : f i j ≤ ∑ t, cell i j t := by
    by_cases h : i = j
    · simp [f,h]
    · obtain ⟨t,ha,hb⟩ := cover i j h
      have bound := Finset.single_le_sum (f := cell i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      simpa [f,h,cell,ha,hb] using bound
  have box (t : Fin k) : ∑ i, ∑ j, cell i j t ≤ 16 := by
    calc
      _ = (∑ i ∈ A t, r i) * ∑ j ∈ B t, c j := by
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        simp [cell,Finset.sum_ite_irrel,
          ite_and]
      _ ≤ 4*4 := Nat.mul_le_mul (rowCap _) (colCap _)
  have upper : ∑ i, ∑ j, f i j ≤ 16*k := by
    calc
      _ ≤ ∑ i, ∑ j, ∑ t, cell i j t := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => once i j
      _ = ∑ t, ∑ i, ∑ j, cell i j t := by
        simp_rw [show ∀ i, (∑ j, ∑ t, cell i j t) = ∑ t, ∑ j, cell i j t from fun i => Finset.sum_comm]
        exact Finset.sum_comm
      _ ≤ ∑ _ : Fin k, 16 := Finset.sum_le_sum (fun t _ => box t)
      _ = _ := by simp [Nat.mul_comm]
  have lo (i j : Fin n) : (if i ≠ j then 8 else 0) ≤ f i j + f j i := by
    by_cases h : i = j
    · simp [h,f]
    · simpa [h,Ne.symm h,f] using crossed (r i) (c i) (r j) (c j) (localBudget i) (localBudget j)
  have raw := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => lo i j))
  have cnt (i : Fin n) : (∑ j : Fin n, if i ≠ j then 8 else 0) = (n-1)*8 := by
    rw [←Finset.sum_filter]
    have e : Finset.univ.filter (fun j : Fin n => i ≠ j) = Finset.univ.erase i := by
      ext j; simp [ne_comm]
    simp [e]
  simp_rw [cnt, Finset.sum_add_distrib] at raw
  have swap : (∑ i, ∑ j, f j i) = ∑ i, ∑ j, f i j := Finset.sum_comm
  rw [swap] at raw
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at raw
  have assoc : n*((n-1)*8) = 8*(n*(n-1)) := by ring
  simp only [Nat.cast_id] at raw
  rw [assoc] at raw
  omega

end CrownWeightedCover
