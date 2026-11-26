import Research.CrownSilentCopies
import Research.CrownSingletonQuarter

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

def silentCopyWires (C : Circuit) (R : Finset (Fin 24)) : Finset ℕ :=
  (Finset.range (24+C.gates.length)).filter (fun a =>
    (C.wires (List.replicate 24 false)).getD a false = false ∧
      ∃ r ∈ R, (C.wires (singleInput r)).getD a false = true)

private theorem diagonal_at_raw : ∀ (i : Fin 12) (r : Fin 24), i ≠ literalLabel r →
    (oneEach i i).getD r.val false = false := by decide

theorem silent_copies_avoid_intact (C : Circuit) (hm : Monotone2 C) (R : Finset (Fin 24))
    (silent : ∀ r ∈ R, (trueOrFlags C.gates (singleInput r)).count true = 0)
    (i : Fin 12) (untouched : i ∉ R.image literalLabel) (a : ℕ) (ha : a ∈ silentCopyWires C R) :
    (C.wires (oneEach i i)).getD a false = false := by
  obtain ⟨_,cold,r,hr,hot⟩ := Finset.mem_filter.mp ha
  exact (silent_cold_is_copy C hm r (silent r hr) a hot cold _ (by simp [oneEach])).trans
    (diagonal_at_raw i r (fun eq => untouched (eq ▸ Finset.mem_image_of_mem _ hr)))

private theorem indexed_sum (gs : List Gate) (f : Gate → Bool) :
    (∑ i : Fin gs.length, if f gs[i] then 1 else 0) = (gs.filter f).length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    change (∑ i : Fin (gs.length+1), if f (g::gs)[i] then 1 else 0) = _
    rw [Fin.sum_univ_succ]
    cases hf : f g <;> simp [hf] at * <;> omega

theorem all_and_count_balance (C : Circuit) (hm : Monotone2 C) :
    (avoidingAnds C ∅).card + (C.gates.filter isOrGate).length = C.size := by
  have eq : (avoidingAnds C ∅).card = (C.gates.filter isAndGate).length := by
    rw [← indexed_sum]
    unfold avoidingAnds
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro k hk
    have emp : C.gates[k].inputs.all (fun a => decide (a ∉ (∅ : Finset ℕ))) = true :=
      List.all_eq_true.mpr (by simp)
    simp only [emp,Bool.and_true]
  rw [eq]
  have count (gs : List Gate) (h : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      (gs.filter isAndGate).length + (gs.filter isOrGate).length = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      have ht := ih (fun f hf => h f (List.mem_cons_of_mem _ hf))
      rcases h g (List.mem_cons_self ..) with hg|hg <;>
        simp [isAndGate,isOrGate,hg] at * <;> omega
  exact count _ (fun g hg => (hm g hg).1)

theorem six_of_silent_incidence (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : 24 ≤ (C.gates.filter isOrGate).length)
    (R : Finset (Fin 24))
    (silent : ∀ r ∈ R, (trueOrFlags C.gates (singleInput r)).count true = 0)
    (inc : 2 * R.card ≤ ((avoidingAnds C ∅) \ (avoidingAnds C (silentCopyWires C R))).card) :
    R.card ≤ 6 := by
  classical
  let S := Finset.univ \ R.image literalLabel
  let D := silentCopyWires C R
  have dead := induced_crown_and_lower C hm rep S D
    (fun i hi => silent_copies_avoid_intact C hm R silent i (Finset.mem_sdiff.mp hi).2)
  have intact : S.card = 12 - (R.image literalLabel).card := by
    dsimp only [S]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  have im := Finset.card_image_le (s := R) (f := literalLabel)
  have subset : avoidingAnds C D ⊆ avoidingAnds C ∅ := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      have h := (Bool.and_eq_true_iff.mp (Finset.mem_filter.mp hk).2).1
      exact Bool.and_eq_true_iff.mpr ⟨h,List.all_eq_true.mpr (by simp)⟩⟩
  have difference := Finset.card_sdiff_of_subset subset
  have cap := all_and_count_balance C hm
  change 2 * R.card ≤ ((avoidingAnds C ∅) \ (avoidingAnds C D)).card at inc
  have kept := Finset.card_le_card subset
  by_contra! bad
  have h₈ : R.card ≤ 8 := by omega
  by_cases eq : R.card = 8
  · have k : (avoidingAnds C D).card = 0 := by omega
    rw [k] at dead
    simp only [pow_zero] at dead
    omega
  · have k : (avoidingAnds C D).card ≤ 2 := by omega
    have ub : 2 ^ (avoidingAnds C D).card ≤ 2^2 := Nat.pow_le_pow_right (by decide) k
    omega
end PEqualNP.Research.MissingCell
