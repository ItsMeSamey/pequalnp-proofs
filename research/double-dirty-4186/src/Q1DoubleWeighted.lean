import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open scoped BigOperators

/-- For positive batches, the sum of the local orientation counts is bounded
by their product. This holds even when a physical slot has many owners. -/
private theorem sum_le_prod_of_two {R : Type*} [DecidableEq R] (w : R → ℕ)
    (hw : ∀ i, 2 ≤ w i) (s : Finset R) : ∑ i ∈ s, w i ≤ ∏ i ∈ s, w i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    by_cases h : s.Nonempty
    · obtain ⟨j,hj⟩ := h
      have hl := Finset.single_le_sum (fun k (_ : k ∈ s) => Nat.zero_le (w k)) hj
      have ha := hw i
      have hb := hw j
      have two : 2 ≤ ∏ k ∈ s, w k := by omega
      have hmul := Nat.mul_le_mul (show 1 ≤ w i-1 by omega)
        (show 1 ≤ (∏ k ∈ s, w k)-1 by omega)
      have e : w i = (w i-1)+1 := by omega
      have f : (∏ k ∈ s, w k) = ((∏ k ∈ s, w k)-1)+1 := by omega
      nlinarith [Nat.sub_add_cancel (show 1 ≤ w i by omega),
        Nat.sub_add_cancel (show 1 ≤ ∏ k ∈ s, w k by omega)]
    · have e := Finset.not_nonempty_iff_eq_empty.mp h
      subst s
      simp

/-- Finite double counting for a shared physical leaf. Each batch has a
local orientation space. Each physical leaf permits at most one orientation
in each batch that uses it. On every full orientation every batch must have
a missed leaf. Other batches impose no restriction. -/
theorem weighted_leaf_count {R L : Type*} [Fintype R] [Fintype L]
    (X : R → Type*) [∀ i, Fintype (X i)] (positive : ∀ i, 2 ≤ Fintype.card (X i))
    (uses : L → Finset R) (miss : ∀ l : L, (i : R) → Finset (X i))
    (uniqueMiss : ∀ l i, i ∈ uses l → (miss l i).card ≤ 1)
    (reject : ∀ t : ∀ i, X i, ∀ i, ∃ l, i ∈ uses l ∧ ∀ k ∈ uses l, t k ∈ miss l k) :
    (∑ i, Fintype.card (X i)) ≤ Fintype.card L := by
  classical
  let w (i : R) := Fintype.card (X i)
  let M := Fintype.card (∀ i, X i)
  let box (l : L) := Fintype.piFinset fun i => if i ∈ uses l then miss l i else Finset.univ
  let weight (l : L) := ∑ i ∈ uses l, w i
  have cap (l : L) : (box l).card * weight l ≤ M := by
    have hbox : (box l).card ≤ ∏ i ∈ (uses l)ᶜ, w i := by
      unfold box
      rw [Fintype.card_piFinset, ← Finset.prod_mul_prod_compl (uses l)]
      have h₁ : (∏ i ∈ uses l, (if i ∈ uses l then miss l i else Finset.univ).card) ≤ 1 := by
        calc
          _ ≤ ∏ _i ∈ uses l, (1 : ℕ) := Finset.prod_le_prod' fun i hi => by simpa [hi] using uniqueMiss l i hi
          _ = _ := by simp
      have h₂ : (∏ i ∈ (uses l)ᶜ, (if i ∈ uses l then miss l i else Finset.univ).card) =
          ∏ i ∈ (uses l)ᶜ, w i := Finset.prod_congr rfl fun i hi => by
            simp [Finset.mem_compl.mp hi,w]
      rw [h₂]
      simpa using Nat.mul_le_mul_right (∏ i ∈ (uses l)ᶜ, w i) h₁
    calc
      _ ≤ (∏ i ∈ (uses l)ᶜ, w i) * ∏ i ∈ uses l, w i :=
        Nat.mul_le_mul hbox (sum_le_prod_of_two w positive (uses l))
      _ = M := by rw [mul_comm, Finset.prod_mul_prod_compl]; simp [M,w,Fintype.card_pi]
  let score (t : ∀ i, X i) (l : L) (i : R) :=
    if t ∈ box l ∧ i ∈ uses l then w i else 0
  have cover (t : ∀ i, X i) : (∑ i, w i) ≤ ∑ l, if t ∈ box l then weight l else 0 := by
    calc
      _ ≤ ∑ i, ∑ l, score t l i := Finset.sum_le_sum fun i _ => by
        obtain ⟨l,hl,rest⟩ := reject t i
        have hbox : t ∈ box l := Fintype.mem_piFinset.mpr fun j => by
          by_cases hj : j ∈ uses l
          · simpa [hj] using rest j hj
          · simp [hj]
        have h := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset L)) =>
          Nat.zero_le (score t k i)) (Finset.mem_univ l)
        simpa [score,hbox,hl] using h
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        by_cases h : t ∈ box l
        · simp [score,h,weight,← Finset.sum_filter]
        · simp [score,h]
  have big : M * (∑ i, w i) ≤ M * Fintype.card L := by
    calc
      _ = ∑ _t : ∀ i, X i, ∑ i, w i := by simp [M]
      _ ≤ ∑ t : ∀ i, X i, ∑ l, if t ∈ box l then weight l else 0 :=
        Finset.sum_le_sum fun t _ => cover t
      _ = ∑ l, (box l).card * weight l := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        simp [← Finset.sum_filter]
      _ ≤ ∑ _l : L, M := Finset.sum_le_sum fun l _ => cap l
      _ = _ := by simp [Nat.mul_comm]
  have pos : 0 < M := by
    rw [show M = ∏ i, w i by simp [M,w,Fintype.card_pi]]
    exact Finset.prod_pos (fun i _ => by have := positive i; dsimp [w]; omega)
  exact Nat.le_of_mul_le_mul_left big pos

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
