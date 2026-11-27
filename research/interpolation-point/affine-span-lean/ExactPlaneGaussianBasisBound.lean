import ExactPlaneAcceptedSmallWitness
namespace ExactPlaneGaussianBasisBound
open Module Submodule ExactPlanePhysicalConverse ExactPlaneResidualPivots ExactPlaneObservedSpan
variable {K : Type*} [AddCommGroup K] [Module F K] {N : ℕ}
theorem bound (priv : Fin N→K) (tag h : Fin N→Plane) (A B : Finset (Fin N))
    (ok : ExactTrace priv tag h A)
    (basis : LinearIndependent F (fun i : ↥B=>(priv i.val,tag i.val,h i.val)))
    (same : physicalSpan priv tag h B=physicalSpan priv tag h A) :
    ExactTrace priv tag h B ∧ B.card≤finrank F (observed priv)+2 := by
  obtain ⟨small,_,sp,_,cap⟩ := ExactPlaneAcceptedSmallWitness.physical priv tag h A ok
  constructor
  · intro z y
    rw [same]
    exact ok z y
  · let colB : ↥B → K × (Plane × Plane) := fun i => (priv i.val,tag i.val,h i.val)
    let colS : ↥small → K × (Plane × Plane) := fun i => (priv i.val,tag i.val,h i.val)
    have big : finrank F (physicalSpan priv tag h B)=B.card := by
      change finrank F (span F (Set.range colB))=B.card
      rw [finrank_span_eq_card (b:=colB) basis,Fintype.card_coe]
    have lo : finrank F (physicalSpan priv tag h small)≤small.card := by
      change (Set.range colS).finrank F≤small.card
      exact (finrank_range_le_card (R:=F) colS).trans_eq (Fintype.card_coe _)
    rw [←big,same,←sp]
    exact lo.trans cap
#print axioms bound
end ExactPlaneGaussianBasisBound
