import ExactPlaneMatchedBasis
import Mathlib.LinearAlgebra.Dimension.Constructions
namespace ExactPlaneSectionComplement
open Module Submodule
variable {F I K : Type*} [Field F] [AddCommGroup K] [Module F K] [Module.Finite F K]

/-- The left basis labels are prescribed vectors, including arbitrary sums of
physical keys. Only complementary basis labels require actual matched sites. -/
theorem indexed {r : Nat} (k : I→K) (S : Finset I)
    (spanS : span F (k '' (S:Set I))=⊤)
    (u : Fin r→K) (ind : LinearIndependent F u) :
    ∃ (idx : Fin (finrank F K-r) → I)
      (D : Basis (Fin r ⊕ Fin (finrank F K-r)) F K),
      Function.Injective idx ∧ (∀ j,idx j∈S) ∧
      (∀ i,D (.inl i)=u i) ∧ ∀ j,D (.inr j)=k (idx j) := by
  classical
  let V := Set.range u ∪ k '' (S:Set I)
  have lower : Set.range u⊆V := Set.subset_union_left
  have spans : ⊤≤span F V := by
    calc
      ⊤ = span F (k '' (S:Set I)) := spanS.symm
      _ ≤ span F V := span_mono Set.subset_union_right
  let U := ind.linearIndepOn_id.extend lower
  let B : Basis U F K := Basis.extendLe ind.linearIndepOn_id lower spans
  have label (x : U) : B x=x.val := Basis.extendLe_apply_self ..
  have inside : Set.range u⊆U := ind.linearIndepOn_id.subset_extend lower
  have chosen : U⊆V := ind.linearIndepOn_id.extend_subset lower
  let P := {x : U // x.val∉Set.range u}
  let incl : Fin r → U := fun i => ⟨u i,inside ⟨i,rfl⟩⟩
  let split : Fin r ⊕ P → U := Sum.elim incl Subtype.val
  have spInj : Function.Injective split := by
    intro a b eq
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (ind.injective (congrArg Subtype.val eq))
      | inr q =>
        exact False.elim (q.property ⟨i,congrArg Subtype.val eq⟩)
    | inr p =>
      cases b with
      | inl j =>
        exact False.elim (p.property ⟨j,(congrArg Subtype.val eq).symm⟩)
      | inr q => exact congrArg Sum.inr (Subtype.ext eq)
  have spSurj : Function.Surjective split := by
    intro x
    by_cases h : x.val∈Set.range u
    · obtain ⟨i,hi⟩ := h
      exact ⟨.inl i,Subtype.ext hi⟩
    · exact ⟨.inr ⟨x,h⟩,rfl⟩
  let e : Fin r ⊕ P ≃ U := Equiv.ofBijective split ⟨spInj,spSurj⟩
  letI : Finite U := Module.Finite.finite_basis B
  letI := Fintype.ofFinite U
  letI : Fintype P := Fintype.ofFinite P
  have cd := Fintype.card_congr e
  rw [Fintype.card_sum,Fintype.card_fin] at cd
  have size := Module.finrank_eq_card_basis B
  have cnt : Fintype.card P=finrank F K-r := by omega
  let f : P ≃ Fin (finrank F K-r) := Fintype.equivFinOfCardEq cnt
  let iso : (Fin r ⊕ Fin (finrank F K-r)) ≃ U := (Equiv.sumCongr (Equiv.refl _) f.symm).trans e
  let D := B.reindex iso.symm
  have left (i : Fin r) : D (.inl i)=u i := by
    rw [show D (.inl i)=B (iso (.inl i)) from Basis.reindex_apply ..,label]
    rfl
  have right (j : Fin (finrank F K-r)) : D (.inr j)=(f.symm j).val.val := by
    rw [show D (.inr j)=B (iso (.inr j)) from Basis.reindex_apply ..,label]
    rfl
  have rep (j : Fin (finrank F K-r)) : ∃ i∈S,k i=D (.inr j) := by
    rw [right]
    exact (chosen (f.symm j).val.property).resolve_left (f.symm j).property
  choose idx mem tagged using rep
  refine ⟨idx,D,?_,mem,left,fun j=>(tagged j).symm⟩
  intro i j eq
  have h := D.injective ((tagged i).symm.trans ((congrArg k eq).trans (tagged j)))
  exact Sum.inr.inj h

#print axioms indexed
end ExactPlaneSectionComplement
