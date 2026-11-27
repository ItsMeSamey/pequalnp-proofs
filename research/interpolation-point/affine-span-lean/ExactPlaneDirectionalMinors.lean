import ExactPlaneCosetDegree
import ExactPlaneDeterminantProfile

namespace ExactPlaneDirectionalMinors
open ExactPlaneSubsetPolynomial ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit
open ExactPlaneCosetDegree ExactPlaneDeterminantProfile
variable {I J G : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype G]

private theorem combine {b : Vec J} {v : I → Vec J} (f : G → Pair J)
    (a t : G → F) {d : ℕ} (minor : ∀ i j,∃ p : Coeff I,degreeLE d p ∧
      ∀ A,eval p A=eval (detANF (f i) (f j)) (support (coset b v A))) :
    ∃ p : Coeff I, degreeLE d p ∧ ∀ A,eval p A=
      eval (detANF (combo f a) (combo f t)) (support (coset b v A)) := by
  classical
  choose q deg eq using minor
  refine ⟨lc a (fun i => lc t (q i)),?_,?_⟩
  · intro U high
    simp [lc,fun i j => deg i j U high]
  · intro A
    rw [← expansion_eval]
    simp only [expansion,eval_lc,eq]

theorem positive (V : Submodule F (Vec J)) (b : Vec J) (v : I→Vec J)
    (inside : ∀ i,v i∈V) (f : G→Pair J) (a t : G→F) (d : ℕ)
    (cert : ∀ i j u, u∈V → HasDegree
      (derivative (fun x => eval (detANF (f i) (f j)) (support x)) u) d) :
    ∃ p : Coeff I, degreeLE (d+1) p ∧ ∀ A,eval p A=
      eval (detANF (combo f a) (combo f t)) (support (coset b v A)) :=
  combine f a t fun i j => ExactPlaneCosetDegree.positive b v _ d
    (fun l => cert i j _ (inside l))

theorem period (V : Submodule F (Vec J)) (b : Vec J) (v : I→Vec J)
    (inside : ∀ i,v i∈V) (f : G→Pair J) (a t : G→F)
    (cert : ∀ i j u, u∈V → ∀ x,
      derivative (fun z => eval (detANF (f i) (f j)) (support z)) u x=0) :
    ∃ p : Coeff I,degreeLE 0 p ∧ ∀ A,eval p A=
      eval (detANF (combo f a) (combo f t)) (support (coset b v A)) :=
  combine f a t fun i j => ExactPlaneCosetDegree.period b v _
    (fun l => cert i j _ (inside l))

#print axioms positive
#print axioms period
end ExactPlaneDirectionalMinors
