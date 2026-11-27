import ExactPlaneExecutableCompression
namespace ExactPlaneExecutableSelector
open ExactPlanePhysicalConverse ExactPlaneResidualPivots ExactPlaneObservedSpan
variable {K : Type*} [AddCommGroup K] [Module F K] [DecidableEq K] {N : ℕ}

theorem compact_decision (priv : Fin N→K) (tag : Fin N→Plane) :
    let R := 2*(ExactPlaneFullDirections.deficit F (key priv) tag+2)+1
    ∃ seed : List (Fin N→Plane),seed.length≤max 1 ((2*(Module.finrank F (observed priv)*2)*2^R)^2) ∧
      ∀ height : Fin N→Plane,
        (∃ A : Finset (Fin N), ExactTrace priv tag height A) ↔
        ∃ (q : Fin N→Plane) (B : Finset (Fin N)),
          runCompact seed priv tag height=some (q,B) ∧ B⊆accept (fun g i=>g i) tag q ∧
          ExactTrace priv tag height B ∧ B.card≤Module.finrank F (observed priv)+2 := by
  intro R
  obtain ⟨seed,size,decision⟩ := exists_complete_seed priv tag
  refine ⟨seed,size,?_⟩
  intro height
  constructor
  · intro yes
    have success := (decision height).mpr yes
    cases h : run seed priv tag height with
    | none => exact False.elim (success h)
    | some ans =>
      obtain ⟨q,A⟩ := ans
      obtain ⟨B,ret,sub,ok,cap⟩ := runCompact_spec h
      exact ⟨q,B,ret,(run_some h).1 ▸ sub,ok,cap⟩
  · rintro ⟨_,B,_,_,hit,_⟩
    exact ⟨B,hit⟩
#print axioms compact_decision
end ExactPlaneExecutableSelector
