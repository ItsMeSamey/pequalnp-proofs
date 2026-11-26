import ExactPlaneGlobalApplication
import ExactPlaneObservedSpan
namespace ExactPlaneGlobalApplication
open Module ExactPlanePhysicalConverse ExactPlaneResidualPivots ExactPlaneObservedSpan
open scoped BigOperators
open Classical
variable {K : Type*} [AddCommGroup K] [Module (ZMod 2) K] {N : ℕ}

private theorem original_sum (priv : Fin N→K) (tag height : Fin N→Plane)
    (U : Finset (Fin N)) (r : Plane)
    (eq : ∑ i∈U,ExactPlanePhysicalResidual.col (key priv) tag height i=(0,0,r)) :
    ∑ i∈U,ExactPlanePhysicalResidual.col priv tag height i=(0,0,r) := by
  let f := (observed priv).subtype.prodMap (LinearMap.id (R:=ZMod 2) (M:=Plane×Plane))
  have transfer := congrArg f eq
  rw [map_sum] at transfer
  exact transfer

theorem raw_decision_iff (priv : Fin N→K) (tag : Fin N→Plane) :
    let R := 2*(ExactPlaneFullDirections.deficit (ZMod 2) (key priv) tag+2)+1
    ∃ S : Finset (observed priv→ₗ[ZMod 2] Plane),
      S.card≤max 1 ((2*(finrank (ZMod 2) (observed priv)*2)*2^R)^2) ∧
      ∀ height : Fin N→Plane,
        (∃ A : Finset (Fin N),ExactTrace priv tag height A) ↔
          ∃ m : List (observed priv→ₗ[ZMod 2] Plane),(∀ g∈m,g∈S) ∧
            (m.length=1 ∨ m.length=3 ∨ m.length=5) ∧
            let A := accepted (key priv) tag m.sum
            ExactTrace priv tag height A ∧
              ∃ (U : Fin 2→Finset (Fin N)) (v : Fin 2→Plane),LinearIndependent (ZMod 2) v ∧
                (∀ j,U j⊆A) ∧ (∀ j,∑ i∈U j,ExactPlanePhysicalResidual.col priv tag height i=(0,0,v j)) ∧
                U 0≠U 1 := by
  intro R
  letI := ExactPlaneObservedSpan.finite priv
  obtain ⟨S,cap,decision⟩ := physical_decision_iff (key priv) tag (full priv)
  refine ⟨S,cap,?_⟩
  intro height
  constructor
  · rintro ⟨A,trace⟩
    obtain ⟨m,mem,len,ok⟩ := (decision height).mp ⟨A,(trace_iff priv tag height A).mpr trace⟩
    obtain ⟨raw,U,v,ind,sub,real,ne⟩ := ok
    exact ⟨m,mem,len,(trace_iff priv tag height _).mp raw,U,v,ind,sub,
      fun j=>original_sum priv tag height _ _ (real j),ne⟩
  · rintro ⟨m,_,_,ok⟩
    exact ⟨_,ok.1⟩
#print axioms raw_decision_iff
end ExactPlaneGlobalApplication
