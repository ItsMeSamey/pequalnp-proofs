import ExactPlaneMatchedBasis
import Mathlib.LinearAlgebra.Dimension.Constructions
namespace ExactPlaneMatchedBasis
open Module Submodule
open Classical
variable {F I K B : Type*} [Field F] [Fintype I] [AddCommGroup K] [Module F K]
  [Module.Finite F K] [AddCommGroup B] [Module F B]

/-- The chart changes may rescue partial directions. Every prescribed
    fully-tagged direction is always available under the final chart. -/
theorem prescribed_basis (k : I→K) (b : I→B) (A : Finset I)
    (g₀ : K →ₗ[F] B) (old : ∀ i∈A,g₀ (k i)=b i) (full : span F (Set.range k)=⊤)
    (D₀ : Finset K) (ind : LinearIndepOn F id (D₀:Set K))
    (alltags : ∀ x∈D₀,∀ t : B,∃ i,k i=x ∧ b i=t) :
    ∃ (g : K →ₗ[F] B) (T : Finset K) (D : Basis T F K) (idx : T→I),
      (∀ i∈A,g (k i)=b i) ∧ D₀⊆T ∧
      (∀ j,D j=j.val) ∧ (∀ j,k (idx j)=D j ∧ b (idx j)=g (D j)) ∧
      (T \ D₀).card=finrank F K-finrank F (span F (D₀:Set K)) := by
  classical
  obtain ⟨g,S,sub,agree,sp⟩ := extend_matches k b A g₀ old full
  let V := (k '' (S:Set I)) ∪ (D₀:Set K)
  have vspan : ⊤≤span F V := by
    calc
      ⊤ = span F (k '' (S:Set I)) := sp.symm
      _ ≤ span F V := span_mono Set.subset_union_left
  have within : (D₀:Set K)⊆V := Set.subset_union_right
  let D := Basis.extendLe ind within vspan
  let U := ind.extend within
  have rD : Set.range D=U := Basis.range_extendLe ind within vspan
  have uf : U.Finite := by
    have hfin : V.Finite := (S.finite_toSet.image k).union D₀.finite_toSet
    exact hfin.subset (ind.extend_subset within)
  let T := uf.toFinset
  have same : (T:Set K)=U := Set.Finite.coe_toFinset uf
  let e : U ≃ T := ⟨fun j => ⟨j.val,by change j.val ∈ (T : Set K); rw [same]; exact j.property⟩,
    fun j => ⟨j.val,by rw [←same]; exact j.property⟩,fun _ => rfl,fun _ => rfl⟩
  let D' : Basis T F K := D.reindex e
  have de (j : T) : D' j=j.val := by
    rw [show D' j=D (e.symm j) from Basis.reindex_apply ..]
    rw [Basis.extendLe_apply_self]
    rfl
  have inc : D₀⊆T := by
    intro x hx
    change x∈(T:Set K)
    rw [same]
    exact ind.subset_extend within hx
  have pick (j : T) : ∃ i,k i=D' j ∧ b i=g (D' j) := by
    rw [de]
    have jU : j.val∈U := by rw [←same]; exact j.property
    rcases (ind.extend_subset within jU) with h|h
    · obtain ⟨i,hi,eq⟩ := h
      exact ⟨i,eq,(agree i hi).symm.trans (congrArg g eq)⟩
    · exact alltags _ h _
  choose idx picked using pick
  refine ⟨g,T,D',idx,fun i hi => agree i (sub hi),inc,de,picked,?_⟩
  have sizeT := Module.finrank_eq_card_basis D'
  rw [Fintype.card_coe] at sizeT
  rw [Finset.card_sdiff_of_subset inc,←sizeT,finrank_span_finset_eq_card ind]
end ExactPlaneMatchedBasis

namespace ExactPlaneMatchedBasis
open Module Submodule
variable {F K : Type*} [Field F] [AddCommGroup K] [Module F K]

theorem outside_not_full (D₀ T : Finset K) (D : Basis T F K) (sub : D₀⊆T)
    (de : ∀ j,D j=j.val) (Full : K→Prop)
    (spans : ∀ x,Full x → x∈span F (D₀:Set K)) (j : T) (out : j.val∉D₀) :
    ¬Full j.val := by
  intro h
  let ids : Set T := {i | i.val∈D₀}
  have miss : j∉ids := out
  have apart := D.linearIndependent.notMem_span_image miss
  have ssub : (D₀:Set K)⊆D '' ids := by
    intro x hx
    exact ⟨⟨x,sub hx⟩,hx,de _⟩
  apply apart
  rw [de]
  exact span_mono ssub (spans _ h)
end ExactPlaneMatchedBasis
