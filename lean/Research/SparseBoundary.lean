import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

namespace SparseBoundary

theorem dominate_subset {V : Type*} [DecidableEq V] (q : ℕ) (A H : Finset V) (S : Finset ℕ)
    (P : ℕ → Finset V) (star : H.card = q+1) (width : S.card ≤ q)
    (small_or_out : ∀ i ∈ S, (P i).card ≤ 1 ∨ ¬ P i ⊆ A) :
    ∃ l ∈ H, ∃ T : Finset V, T.card ≤ q ∧ Disjoint T A ∧
      ∀ i ∈ S, l ∈ P i → ∃ t ∈ T, t ∈ P i := by
  classical
  let small := S.filter (fun i => (P i).card ≤ 1)
  have sc : small.card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
  have uc : (small.biUnion P).card ≤ q := by
    have own (i : ℕ) (hi : i ∈ small) : (P i).card ≤ 1 := (Finset.mem_filter.mp hi).2
    calc
      _ ≤ ∑ i ∈ small, (P i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ small, 1 := Finset.sum_le_sum own
      _ ≤ q := by simpa using le_trans sc width
  have fresh : ∃ l ∈ H, l ∉ small.biUnion P := by
    by_contra! h
    have := Finset.card_le_card h
    omega
  obtain ⟨l,hl,away⟩ := fresh
  let active := S.filter (fun i => l ∈ P i)
  have find (i : active) : ∃ t ∈ P i.val, t ∉ A := by
    obtain ⟨ins,contains⟩ := Finset.mem_filter.mp i.property
    rcases small_or_out i.val ins with singleton|out
    · exact False.elim (away (Finset.mem_biUnion.mpr
        ⟨i.val,Finset.mem_filter.mpr ⟨ins,singleton⟩,contains⟩))
    · exact Finset.not_subset.mp out
  let f (i : active) := (find i).choose
  let T := Finset.univ.image f
  have tc : T.card ≤ active.card := by
    simpa [T] using (Finset.card_image_le (f := f) (s := Finset.univ))
  have ac : active.card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
  refine ⟨l,hl,T,by omega,Finset.disjoint_left.mpr ?_,?_⟩
  · intro t ht
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
    exact (find i).choose_spec.2
  · intro i hi hit
    let j : active := ⟨i,Finset.mem_filter.mpr ⟨hi,hit⟩⟩
    exact ⟨f j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,(find j).choose_spec.1⟩

theorem dominate {V : Type*} [DecidableEq V] (q : ℕ) (A : Finset V) (S : Finset ℕ)
    (P : ℕ → Finset V) (star : A.card = q+1) (width : S.card ≤ q)
    (small_or_out : ∀ i ∈ S, (P i).card ≤ 1 ∨ ¬ P i ⊆ A) :
    ∃ l ∈ A, ∃ T : Finset V, T.card ≤ q ∧ Disjoint T A ∧
      ∀ i ∈ S, l ∈ P i → ∃ t ∈ T, t ∈ P i :=
  dominate_subset q A A S P star width small_or_out

end SparseBoundary
