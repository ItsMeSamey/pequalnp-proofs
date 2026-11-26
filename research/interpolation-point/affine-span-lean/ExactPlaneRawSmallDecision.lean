import ExactPlaneRawApplication
import ExactPlaneAcceptedSmallWitness
namespace ExactPlaneAcceptedSmallWitness
open Module ExactPlanePhysicalConverse ExactPlaneResidualPivots ExactPlaneObservedSpan
open ExactPlaneGlobalApplication
open scoped BigOperators
variable {K : Type*} [AddCommGroup K] [Module (ZMod 2) K] {N : Nat}

theorem observed_chart (k : Fin N→K) (tag h : Fin N→Plane) (g : observed k→ₗ[ZMod 2] Plane)
    (hit : ExactTrace k tag h (accepted (key k) tag g)) :
    ∃ S : Finset (Fin N), S⊆accepted (key k) tag g ∧
      (∀ i∈S,tag i=g (key k i)) ∧
      physicalSpan k tag h S=physicalSpan k tag h (accepted (key k) tag g) ∧
      ExactTrace k tag h S ∧ S.card≤finrank (ZMod 2) (observed k)+2 := by
  obtain ⟨S,sub,eq,ok,bd⟩ := physical k tag h _ hit
  exact ⟨S,sub,fun _ hi => (Finset.mem_filter.mp (sub hi)).2,eq,ok,bd⟩

theorem raw_small_decision (priv : Fin N→K) (tag : Fin N→Plane) :
    let R := 2*(ExactPlaneFullDirections.deficit (ZMod 2) (key priv) tag+2)+1
    ∃ S : Finset (observed priv→ₗ[ZMod 2] Plane),
      S.card≤max 1 ((2*(finrank (ZMod 2) (observed priv)*2)*2^R)^2) ∧
      ∀ height : Fin N→Plane,
        (∃ A : Finset (Fin N),ExactTrace priv tag height A) ↔
          ∃ m : List (observed priv→ₗ[ZMod 2] Plane),(∀ g∈m,g∈S) ∧
            (m.length=1 ∨ m.length=3 ∨ m.length=5) ∧
            ∃ A' : Finset (Fin N), A'⊆accepted (key priv) tag m.sum ∧
              physicalSpan priv tag height A'=physicalSpan priv tag height (accepted (key priv) tag m.sum) ∧
              ExactTrace priv tag height A' ∧ A'.card≤finrank (ZMod 2) (observed priv)+2 := by
  classical
  intro R
  obtain ⟨S,cap,decision⟩ := raw_decision_iff priv tag
  refine ⟨S,cap,?_⟩
  intro h
  constructor
  · intro hit
    obtain ⟨m,mem,len,ok⟩ := (decision h).mp hit
    obtain ⟨A',sub,_,eq,trace,bd⟩ := observed_chart priv tag h m.sum ok.1
    exact ⟨m,mem,len,A',sub,eq,trace,bd⟩
  · rintro ⟨_,_,_,A',_,_,trace,_⟩
    exact ⟨A',trace⟩
#print axioms observed_chart
#print axioms raw_small_decision
end ExactPlaneAcceptedSmallWitness
