import Mathlib.Data.Finset.Max
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Finset.Card

namespace CrownLabelCap

def weight (n : ℕ) : ℕ := 4 / 2 ^ n

theorem weight_table {n : ℕ} (h : n ≤ 2) :
    weight n = if n = 0 then 4 else if n = 1 then 2 else 1 := by
  interval_cases n <;> decide

theorem cards (A B : Finset ℕ) (h : (A ∪ B).card ≤ 2) :
    A.card ≤ 2 ∧ B.card ≤ 2 := by
  exact ⟨(Finset.card_le_card Finset.subset_union_left).trans h,
    (Finset.card_le_card Finset.subset_union_right).trans h⟩

theorem S (A B : Finset ℕ) (ha : A.card = 2) (hb : B.card = 2) :
    weight A.card + weight B.card = 2 := by
  rw [ha,hb]; decide

theorem W (A B : Finset ℕ) (h : (A ∪ B).card ≤ 2)
    (hw : ¬ (A.card = 2 ∧ B.card = 2)) :
    3 ≤ weight A.card + weight B.card := by
  obtain ⟨a,b⟩ := cards A B h
  rw [weight_table a, weight_table b]
  split_ifs <;> omega

/-- If the minima differ, the later side is a singleton. If they also
overlap, the earlier side contains both first indices. -/
theorem N_shape {α : Type*} [LinearOrder α] (A B : Finset α) (i j : α) (hi : i ∈ A) (hj : j ∈ B)
    (lt : i < j) (firstB : ∀ x ∈ B, j ≤ x) (meet : (A ∩ B).Nonempty)
    (h : (A ∪ B).card ≤ 2) : A = {i,j} ∧ B = {j} := by
  have hij : i ≠ j := ne_of_lt lt
  have sub : ({i,j} : Finset α) ⊆ A ∪ B := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_union_left _ hi
    · exact Finset.mem_union_right _ hj
  have un := Finset.eq_of_subset_of_card_le sub (by simpa [hij] using h)
  have hb : B = {j} := by
    ext x
    simp only [Finset.mem_singleton]
    constructor
    · intro hx
      have hu := Finset.mem_union_right A hx
      rw [← un] at hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact (lt.not_ge (firstB _ hx)).elim
      · rfl
    · rintro rfl
      exact hj
  have ja : j ∈ A := by
    obtain ⟨x,hx⟩ := meet
    obtain ⟨hxA,hxB⟩ := Finset.mem_inter.mp hx
    rw [hb, Finset.mem_singleton] at hxB
    exact hxB ▸ hxA
  refine ⟨Finset.Subset.antisymm ?_ ?_, hb⟩
  · rw [un]
    exact Finset.subset_union_left
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hi
    · exact ja

theorem N (A B : Finset ℕ) (i j : ℕ) (hi : i ∈ A) (hj : j ∈ B)
    (lt : i < j) (firstB : ∀ x ∈ B, j ≤ x) (meet : (A ∩ B).Nonempty)
    (h : (A ∪ B).card ≤ 2) :
    weight A.card = 1 ∧ weight B.card = 2 ∧ 2 + weight B.card = 4 := by
  obtain ⟨ha,hb⟩ := N_shape A B i j hi hj lt firstB meet h
  simp [ha,hb,Nat.ne_of_lt lt,weight]

theorem D (A B : Finset ℕ) (a : A.Nonempty) (b : B.Nonempty)
    (hd : Disjoint A B) (h : (A ∪ B).card ≤ 2) :
    weight A.card + weight B.card = 4 := by
  rw [Finset.card_union_of_disjoint hd] at h
  have ap := Finset.card_pos.mpr a
  have bp := Finset.card_pos.mpr b
  rw [show A.card = 1 by omega, show B.card = 1 by omega]
  decide

theorem Z (A B : Finset ℕ) (he : A = ∅ ∨ B = ∅) (h : (A ∪ B).card ≤ 2) :
    5 ≤ weight A.card + weight B.card := by
  obtain ⟨a,b⟩ := cards A B h
  rw [weight_table a, weight_table b]
  rcases he with rfl | rfl <;> simp only [Finset.card_empty] <;> split_ifs <;> omega

/-- This disjoint classification includes every choice of two signatures.
The two intermediate classes W and N have the same uncorrected cap. -/
def baseFloor (A B : Finset ℕ) : ℕ :=
  if A = ∅ ∨ B = ∅ then 5
  else if Disjoint A B then 4
  else if A = B ∧ A.card = 2 then 2 else 3

theorem base_floor_le (A B : Finset ℕ) (h : (A ∪ B).card ≤ 2) :
    baseFloor A B ≤ weight A.card + weight B.card := by
  unfold baseFloor
  split_ifs with empty disj same
  · exact Z _ _ empty h
  · have ha : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun e => empty (Or.inl e))
    have hb : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun e => empty (Or.inr e))
    exact (D _ _ ha hb disj h).ge
  · obtain ⟨rfl,ha⟩ := same
    exact (S _ _ ha ha).ge
  · apply W _ _ h
    rintro ⟨ha,hb⟩
    have eqA := Finset.eq_of_subset_of_card_le (Finset.subset_union_left (s₂ := B) (s₁ := A))
      (h.trans (by omega : 2 ≤ A.card))
    have eqB := Finset.eq_of_subset_of_card_le (Finset.subset_union_right (s₂ := B) (s₁ := A))
      (h.trans (by omega : 2 ≤ B.card))
    exact same ⟨eqA.trans eqB.symm, ha⟩

end CrownLabelCap
