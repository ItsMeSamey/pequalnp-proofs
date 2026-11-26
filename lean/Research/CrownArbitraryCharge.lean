import Research.CrownRawCharge

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def weightedWireMass (C : Circuit) (w : Fin 24 → ℚ) (a : ℕ) : ℚ :=
  ∑ t ∈ Finset.univ.filter (fun t : Fin 24 => (C.wires (singleInput t)).getD a false), w t

theorem weightedWireMass_split (C : Circuit) (w : Fin 24 → ℚ) (a : ℕ) : weightedWireMass C w a =
    (∑ u ∈ rowSupport C a, w (rowPort u)) +
      ∑ v ∈ colSupport C a, w (colPort v) := by
  simp only [weightedWireMass,rowSupport,colSupport,Finset.sum_filter]
  exact Fin.sum_univ_add (a := 12) (b := 12) _

theorem crown_arbitrary_edge_charge (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) (w : Fin 24 → ℚ) (pos : ∀ t, 0 ≤ w t) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin 12 × Fin 12 => p.1 ≠ p.2),
      w (rowPort p.1) * w (colPort p.2) ≤
    ∑ k ∈ Finset.univ.filter (fun k => chargeable C k = true),
      weightedWireMass C w (operand C k 0) * weightedWireMass C w (operand C k 1) := by
  let r (i : Fin 12) := w (rowPort i)
  let c (j : Fin 12) := w (colPort j)
  apply le_trans (CrownCharge.sum_cover _ _ (chargingRect C) (fun p => r p.1*c p.2)
    (fun p => mul_nonneg (pos _) (pos _)) ?_)
  · apply Finset.sum_le_sum
    intro k _
    rw [weightedWireMass_split,weightedWireMass_split]
    exact CrownCharge.crossed_rectangle_bound _ _ _ _ r c (fun _ => pos _) (fun _ => pos _)
  · intro p hp
    obtain ⟨k,_,good,hit⟩ := crown_first_charger C hm rep (Finset.mem_filter.mp hp).2
    exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,good⟩,hit⟩

theorem weightedWireMass_raw (C : Circuit) (w : Fin 24 → ℚ) (t : Fin 24) :
    weightedWireMass C w t.val = w t := by
  simp only [weightedWireMass,Finset.sum_filter,raw_single_support,decide_eq_true_eq]; simp

theorem crown_arbitrary_quarter_charge (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (w : Fin 24 → ℚ) (pos : ∀ t, 0 ≤ w t)
    (capacity : ∀ a, (C.wires (List.replicate 24 false)).getD a false = false → weightedWireMass C w a ≤ 4) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin 12 × Fin 12 => p.1 ≠ p.2), w (rowPort p.1) * w (colPort p.2) ≤
      16 * ((Finset.univ.filter (fun k => chargeable C k = true)).card : ℚ) := by
  apply (crown_arbitrary_edge_charge C hm rep w pos).trans
  calc
    _ ≤ ∑ _k ∈ Finset.univ.filter (fun k => chargeable C k = true), (16 : ℚ) := by
      apply Finset.sum_le_sum
      intro k hk
      have ok := (Finset.mem_filter.mp hk).2
      unfold chargeable at ok
      have h := Bool.and_eq_true_iff.mp ok
      have left := capacity (operand C k 0) (by simpa using (Bool.and_eq_true_iff.mp h.1).2)
      have right := capacity (operand C k 1) (by simpa using h.2)
      simpa only [show (4 : ℚ) * 4 = 16 by norm_num] using mul_le_mul left right (Finset.sum_nonneg (fun t _ => pos t)) (by norm_num)
    _ = _ := by simp [mul_comm]
end PEqualNP.Research.MissingCell
