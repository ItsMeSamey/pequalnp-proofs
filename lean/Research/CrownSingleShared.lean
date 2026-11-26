import Research.CrownCommonParent

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

def parentDiags (C : Circuit) (p : ℕ) : Finset (Fin 12) :=
  Finset.univ.filter (fun i : Fin 12 => (C.wires (oneEach i i)).getD p false)

private theorem active_of_parent (C : Circuit) (p : ℕ) (i : Fin 12) (hi : i ∈ parentDiags C p)
    (a : Fin C.gates.length) (hp : p ∈ readAt C.gates 24 a.val) :
    a ∈ activeOrIds C.gates (oneEach i i) := by
  apply (activeOrIds_iff_final_parent ..).mpr
  exact ⟨p,by simpa [oneEach] using hp,(Finset.mem_filter.mp hi).2⟩

theorem crown_shared_parent_diags_le_one (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    {a b : Fin C.gates.length} (ab : a ≠ b) (p : ℕ)
    (pa : p ∈ readAt C.gates 24 a.val) (pb : p ∈ readAt C.gates 24 b.val) :
    (parentDiags C p).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra ij
  have mn : p ∈ readAt C.gates 24 (min a b).val := by
    rcases le_total a b with h|h
    · simpa only [min_eq_left h] using pa
    · simpa only [min_eq_right h] using pb
  obtain ⟨e,earlier,ei,_⟩ := crown_common_parent C hm rep size ors i j ij (min a b) p mn
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have ea := (lt_of_lt_of_le earlier (min_le_left a b)).ne
  have eb := (lt_of_lt_of_le earlier (min_le_right a b)).ne
  have ai := active_of_parent C p i hi a pa
  have bi := active_of_parent C p i hi b pb
  have sub : ({e,a,b} : Finset _) ⊆ activeOrIds C.gates (oneEach i i) := by
    intro t ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl|rfl|rfl <;> assumption
  have cnt := Finset.card_le_card sub
  simp [ea,eb,ab,activeOrIds_card] at cnt
  have lim := crown_trueOrFlags_le i C hm rep
  omega

theorem crown_collision_saturated_aux (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    {a b : Fin C.gates.length} (ab : a ≠ b) (edge : shareOrRead C a b)
    (parent_bound : ∀ g : Fin C.gates.length, ∀ q ∈ readAt C.gates 24 g.val,
      (parentDiags C q).card ≤ 2) :
    (Finset.univ.filter (fun i : Fin 12 => 2 ≤ (trueOrFlags C.gates (oneEach i i)).count true)).card ≤ 5 := by
  classical
  obtain ⟨p,pa,pb⟩ := edge
  let P (g : Fin C.gates.length) := readAt C.gates 24 g.val
  let D := (P a).erase p ∪ (P b).erase p
  let S := Finset.univ.filter (fun i : Fin 12 => 2 ≤ (trueOrFlags C.gates (oneEach i i)).count true)
  have small (g : Fin C.gates.length) (hp : p ∈ P g) : ((P g).erase p).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hp]
    have H : (P g).card ≤ 2 := readAt_card_le_two _ _ _ (fun z hz => (hm z hz).2)
    omega
  have dsize : D.card ≤ 2 := by
    have H := Finset.card_union_le ((P a).erase p) ((P b).erase p)
    change ((P a).erase p ∪ (P b).erase p).card ≤ 2
    have := small a pa
    have := small b pb
    omega
  have sub : S ⊆ parentDiags C p ∪ D.biUnion (parentDiags C) := by
    intro i hi
    have lo := (Finset.mem_filter.mp hi).2
    have hi' := crown_trueOrFlags_le i C hm rep
    have eq : (trueOrFlags C.gates (oneEach i i)).count true = 2 := by omega
    have cov : a ∈ activeOrIds C.gates (oneEach i i) ∨ b ∈ activeOrIds C.gates (oneEach i i) := by
      by_contra! H
      exact Finset.disjoint_left.mp (crown_inactive_pair_disjoint C hm rep ors i eq a b ab H.1 H.2) pa pb
    have inc (g : Fin C.gates.length) (hg : g = a ∨ g = b) (h : g ∈ activeOrIds C.gates (oneEach i i)) :
        i ∈ parentDiags C p ∪ D.biUnion (parentDiags C) := by
      obtain ⟨q,hq,hit⟩ := (activeOrIds_iff_final_parent ..).mp h
      have hh : q ∈ P g := by simpa [P,oneEach] using hq
      have member : i ∈ parentDiags C q := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩
      by_cases same : q=p
      · exact Finset.mem_union_left _ (same ▸ member)
      · have d : q ∈ D := by
          rcases hg with rfl|rfl
          · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨same,hh⟩)
          · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨same,hh⟩)
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q,d,member⟩)
    exact cov.elim (inc a (Or.inl rfl)) (inc b (Or.inr rfl))
  have one := crown_shared_parent_diags_le_one C hm rep size ors ab p pa pb
  have two (q : ℕ) (hq : q ∈ D) : (parentDiags C q).card ≤ 2 := by
    rcases Finset.mem_union.mp hq with h|h
    · exact parent_bound a q (Finset.mem_erase.mp h).2
    · exact parent_bound b q (Finset.mem_erase.mp h).2
  have f := Finset.card_biUnion_le (s := D) (t := parentDiags C)
  have total := Finset.sum_le_sum two
  have four : (D.biUnion (parentDiags C)).card ≤ 4 := by
    calc
      _ ≤ ∑ q ∈ D, (parentDiags C q).card := f
      _ ≤ ∑ _q ∈ D, 2 := total
      _ ≤ 4 := by simp; omega
  have union := Finset.card_union_le (parentDiags C p) (D.biUnion (parentDiags C))
  exact (Finset.card_le_card sub).trans (by omega)

end PEqualNP.Research.MissingCell
