import ExactPlaneGeneratedDecision
namespace ExactPlaneGeneratedDecision
open ExactPlaneFieldSampler ExactPlaneSuppliedCoordinates ExactPlanePhysicalConverse
open ExactPlaneResidualPivots ExactPlaneObservedSpan

theorem returned {R : Nat} {priv : Fin N→Key d} {tag height q : Fin N→Plane}
    {B : Finset (Fin N)} (h : run R priv tag height=some (q,B)) :
    let A := ExactPlaneExecutableSelector.accept (fun (p : Fin N→Plane) i=>p i) tag q
    B⊆A ∧ physicalSpan priv tag height B=physicalSpan priv tag height A ∧
      ExactTrace priv tag height B ∧ B.card≤Module.finrank (ZMod 2) (observed priv)+2 := by
  let s := tables (siteRows d R) priv
  change ExactPlaneEagerSelector.runBasis s priv tag height=some (q,B) at h
  rw [ExactPlaneEagerSelector.runBasis_eq] at h
  cases g : ExactPlaneGaussianSelector.run s priv tag height with
  | none =>
    change (ExactPlaneGaussianSelector.run s priv tag height).map _=some _ at h
    simp [g] at h
  | some pair =>
    obtain ⟨y,A⟩ := pair
    obtain ⟨T,c,sub,span,ok,count⟩ := ExactPlaneGaussianSelector.runBasis_witness g
    rw [h] at c
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj c)
    have h' : ExactPlaneExecutableSelector.run s priv tag height=some (q,A) := by
      rwa [← ExactPlaneGaussianSelector.run_eq]
    have a := (ExactPlaneExecutableSelector.run_some h').1
    exact a ▸ ⟨sub,span,ok,count⟩

#print axioms returned
end ExactPlaneGeneratedDecision
