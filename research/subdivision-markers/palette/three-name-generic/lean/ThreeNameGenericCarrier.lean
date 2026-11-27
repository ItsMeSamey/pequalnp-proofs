import ThreeNamePackedPins
import ThreeNameChain
namespace ThreeNameGenericCarrier
open ThreeNamePacked ThreeNamePinReduction ThreeNameChain
open scoped BigOperators
/-- A member of an indexed binary span is the XOR of one subset of the original labels. -/
theorem subset_sum {J : Type} [Fintype J] [DecidableEq J] {w : Nat}
    (col : J → Vec w) (A : Finset J) (y : Vec w) (h : y ∈ indexedSpan col A) :
    ∃ S ⊆ A, (∑ i ∈ S, col i) = y := by
  classical
  obtain ⟨mask,hit⟩ := (ExactPlaneGaussian.solve_hits A.toList col y).mpr (by
    simpa [indexedSpan] using h)
  obtain ⟨val,out⟩ := ExactPlaneGaussian.solve_witness A.toList col y mask hit
  refine ⟨A.filter (fun i => mask i = 1),Finset.filter_subset _ _,?_⟩
  have dec : (∑ i, mask i • col i) = y := by
    simpa [ExactPlaneGaussian.decode,LinearMap.sum_apply] using val
  rw [← dec,Finset.sum_filter]
  calc
    _ = ∑ i ∈ A, mask i • col i := by
      apply Finset.sum_congr rfl
      intro i _
      rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) (mask i) with h|h <;> simp [h]
    _ = _ := Finset.sum_subset (Finset.subset_univ _) (by
      intro i _ notin
      have zero := out i (by simpa using notin)
      simp [zero])

/-- Reindex ordinary columns in the padded label type. Selected pins have
zero image and may be dropped. Equal or parallel columns keep their labels. -/
theorem ordinary_span {O J : Type} [DecidableEq O] [DecidableEq J] {w : Nat}
    (col : O → Vec w) (p : Carrier J (Vec w)) (A pins : Finset O) (lift : O ↪ J)
    (same : ∀ i ∈ A \ pins, p.col (lift i) = col i)
    (kill : ∀ i ∈ A ∩ pins, col i = 0) :
    indexedSpan p.col ((A \ pins).image lift) = indexedSpan col A := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨i, hi, rfl⟩
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    rw [same j hj]
    exact Submodule.subset_span ⟨j,(Finset.mem_sdiff.mp hj).1,rfl⟩
  · rintro _ ⟨j,hj,rfl⟩
    by_cases pin : j ∈ pins
    · rw [kill j (Finset.mem_inter.mpr ⟨hj,pin⟩)]
      exact Submodule.zero_mem _
    · have mem := Finset.mem_sdiff.mpr ⟨hj,pin⟩
      rw [← same j mem]
      exact Submodule.subset_span ⟨lift j,Finset.mem_image_of_mem _ mem,rfl⟩

/-- From a selected exact quotient line recover an ordinary padded support
and every zero/full mixed trace needed by the split-chain theorem. -/
theorem ordinary_support {O J B : Type} [DecidableEq O] [Fintype J] [DecidableEq J]
    [AddCommGroup B] [Module (ZMod 2) B] {w : Nat}
    (col : O → Vec w) (p : Carrier J (Vec w)) (roots : Finset J)
    (A pins : Finset O) (lift : O ↪ J)
    (atom : ∀ i ∈ A \ pins, lift i ∈ p.ground ∧ lift i ∉ roots ∧ p.col (lift i) = col i)
    (kill : ∀ i ∈ A ∩ pins, col i = 0)
    (name : (B × ZMod 2) →ₗ[ZMod 2] Vec w) (exactA : Exact col name A)
    (target : name (0,1) = ∑ i ∈ roots,p.col i)
    (named : ∀ P ⊆ roots, ∃ z y, name (z,y) = ∑ i ∈ P,p.col i) :
    ∃ S ⊆ p.ground, Disjoint roots S ∧ (∑ i ∈ S,p.col i) = (∑ i ∈ roots,p.col i) ∧
      ∀ Q ⊆ S, ∀ P ⊆ roots, (∑ i ∈ Q,p.col i) = (∑ i ∈ P,p.col i) →
        (∑ i ∈ P,p.col i) = 0 ∨ (∑ i ∈ P,p.col i) = ∑ i ∈ roots,p.col i := by
  classical
  let T := (A \ pins).image lift
  have spans : indexedSpan p.col T = indexedSpan col A :=
    ordinary_span col p A pins lift (fun i hi => (atom i hi).2.2) kill
  have ex : Exact p.col name T := by
    intro z y
    rw [spans]
    exact exactA z y
  have ground : T ⊆ p.ground := by
    rintro _ h
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
    exact (atom j hj).1
  have dis : Disjoint roots T := Finset.disjoint_left.mpr (by
    intro i hi hm
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hm
    exact (atom j hj).2.1 hi)
  obtain ⟨S,st,sm⟩ := subset_sum p.col T _ ((ex 0 1).mpr rfl)
  refine ⟨S,st.trans ground,Finset.disjoint_left.mpr (fun _ hr hs =>
    Finset.disjoint_left.mp dis hr (st hs)),sm.trans target,?_⟩
  intro Q hq P hp eq
  obtain ⟨z,y,hm⟩ := named P hp
  have belongs : (∑ i ∈ Q,p.col i) ∈ indexedSpan p.col T :=
    Submodule.sum_mem _ (fun i hi => Submodule.subset_span ⟨i,st (hq hi),rfl⟩)
  have namedmem : name (z,y) ∈ indexedSpan p.col T := by
    rw [hm,← eq]
    exact belongs
  have hz := (ex z y).mp namedmem
  subst z
  rw [← hm]
  rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 by decide) y with hy | hy
  · left
    rw [hy]
    exact name.map_zero
  · right
    rwa [hy]

#print axioms ordinary_support
end ThreeNameGenericCarrier
