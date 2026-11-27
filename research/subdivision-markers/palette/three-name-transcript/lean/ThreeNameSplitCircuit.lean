import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ThreeNameSplitCircuit
open scoped BigOperators
variable {ι V : Type*} [DecidableEq ι] [AddCommGroup V]

def Circuit (v : ι → V) (C : Finset ι) : Prop :=
  C.Nonempty ∧ (∑ i ∈ C, v i) = 0 ∧
    ∀ T ⊆ C, T.Nonempty → (∑ i ∈ T, v i) = 0 → T = C

def Independent (v : ι → V) (A : Finset ι) : Prop :=
  ∀ T ⊆ A, T.Nonempty → (∑ i ∈ T, v i) ≠ 0

theorem contained {v u : ι → V} {C : Finset ι} (h : Circuit v C)
    (same : ∀ i ∈ C, u i = v i) : Circuit u C := by
  have eqsum (T : Finset ι) (hT : T ⊆ C) :
      (∑ i ∈ T, u i) = ∑ i ∈ T, v i :=
    Finset.sum_congr rfl (fun i hi => same i (hT hi))
  exact ⟨h.1, (eqsum C (fun _ hi => hi)).trans h.2.1,
    fun T ht hn hz => h.2.2 T ht hn ((eqsum T ht).symm.trans hz)⟩

/-- Both sides of a crossing circuit represent the same nonzero interface
vector. Its fresh label completes the retained side to a circuit through R. -/
theorem crossing {v : ι → V} {A B R : Finset ι} {f : ι}
    (binary : ∀ x : V, x + x = 0) (dis : Disjoint A B)
    (ha : A.Nonempty) (hb : B.Nonempty) (hf : f ∉ A ∪ B) (hr : R ⊆ A)
    (hc : Circuit v (A ∪ B)) :
    let w := ∑ i ∈ A, v i
    let u := fun i => if i = f then w else v i
    Independent v A ∧ w ≠ 0 ∧ w = (∑ i ∈ B, v i) ∧
      Circuit u (insert f A) ∧ R ⊆ insert f A := by
  dsimp only
  have hfa : f ∉ A := fun h => hf (Finset.mem_union_left _ h)
  have hab : (∑ i ∈ A, v i) + (∑ i ∈ B, v i) = 0 := by
    rw [← Finset.sum_union dis]
    exact hc.2.1
  have heq : (∑ i ∈ A, v i) = ∑ i ∈ B, v i := by
    apply add_left_cancel (a := ∑ i ∈ A, v i)
    exact (binary _).trans hab.symm
  have hind : Independent v A := by
    intro T ht hn hz
    have hh := hc.2.2 T (fun _ hi => Finset.mem_union_left _ (ht hi)) hn hz
    obtain ⟨b, hB⟩ := hb
    have hmem : b ∈ T := hh.symm ▸ Finset.mem_union_right A hB
    exact Finset.disjoint_left.mp dis (ht hmem) hB
  let u := fun i => if i = f then (∑ j ∈ A, v j) else v i
  have same (T : Finset ι) (ht : T ⊆ A) :
      (∑ i ∈ T, u i) = ∑ i ∈ T, v i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≠ f := fun eq => hfa (eq ▸ ht hi)
    simp [u, hi']
  refine ⟨hind, hind A (fun _ h => h) ha, heq, ?_, fun _ hi => Finset.mem_insert_of_mem (hr hi)⟩
  change Circuit u (insert f A)
  refine ⟨Finset.insert_nonempty _ _, ?_, ?_⟩
  · rw [Finset.sum_insert hfa, same A (fun _ h => h)]
    simpa [u] using binary (∑ i ∈ A, v i)
  · intro T hT hN hZ
    by_cases hF : f ∈ T
    · let D := T.erase f
      have hd : D ⊆ A := by
        intro i hi
        have hm := Finset.mem_erase.mp hi
        exact (Finset.mem_insert.mp (hT hm.2)).resolve_left hm.1
      have hfd : f ∉ D := Finset.notMem_erase _ _
      have hTD : insert f D = T := Finset.insert_erase hF
      have hzero : (∑ i ∈ D, v i) + (∑ i ∈ B, v i) = 0 := by
        rw [← hTD, Finset.sum_insert hfd, same D hd] at hZ
        simpa [u, ← heq, add_comm] using hZ
      have sub : D ∪ B ⊆ A ∪ B := Finset.union_subset_union hd (fun _ h => h)
      have dj : Disjoint D B := Finset.disjoint_left.mpr
        (fun _ hi hj => Finset.disjoint_left.mp dis (hd hi) hj)
      have eq := hc.2.2 (D ∪ B) sub (hb.mono Finset.subset_union_right) (by
        rw [Finset.sum_union dj]
        exact hzero)
      have hAD : A ⊆ D := by
        intro i hi
        have hm : i ∈ D ∪ B := eq.symm ▸ Finset.mem_union_left B hi
        exact (Finset.mem_union.mp hm).resolve_right (Finset.disjoint_left.mp dis hi)
      rw [← hTD, Finset.Subset.antisymm hd hAD]
    · have ht : T ⊆ A := by
        intro i hi
        exact (Finset.mem_insert.mp (hT hi)).resolve_left (fun eq => hF (eq ▸ hi))
      exact False.elim (hind T ht hN ((same T ht).symm.trans hZ))

#print axioms crossing
#print axioms contained
end ThreeNameSplitCircuit
