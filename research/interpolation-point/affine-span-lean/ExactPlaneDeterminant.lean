import ExactPlaneAffineSpanHit
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
namespace ExactPlaneDeterminant
open ExactPlaneSubsetPolynomial ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit
variable {J : Type*} [Fintype J] [DecidableEq J]

def score (a b c d : Vec J → F) (x : Vec J) : F := a x*d x+b x*c x

def independent (a b c d : Vec J → F) (x : Vec J) : Prop :=
  LinearIndependent F (fun i : Fin 2 => if i=0 then (a x,c x) else (b x,d x))

theorem score_ne_iff (a b c d : Vec J → F) (x : Vec J) :
    score a b c d x≠0 ↔ independent a b c d x := by
  have table : ∀ A B C D : F,A*D+B*C≠0 ↔
      ∀ g : Fin 2→F, (∑ i,g i • (if i=0 then (A,C) else (B,D)))=0 → ∀ i,g i=0 := by decide
  unfold independent
  exact (table (a x) (b x) (c x) (d x)).trans Fintype.linearIndependent_iff.symm

def Quadratic (a : Vec J → F) : Prop :=
  ∃ p : Coeff J, degreeLE 2 p ∧ ∀ x, eval p (support x)=a x

theorem quartic_score {a b c d : Vec J → F}
    (qa : Quadratic a) (qb : Quadratic b) (qc : Quadratic c) (qd : Quadratic d) :
    ∃ p : Coeff J, degreeLE 4 p ∧ ∀ x,eval p (support x)=score a b c d x := by
  obtain ⟨A,dA,hA⟩ := qa
  obtain ⟨B,dB,hB⟩ := qb
  obtain ⟨C,dC,hC⟩ := qc
  obtain ⟨D,dD,hD⟩ := qd
  refine ⟨fun U => product A D U+product B C U,?_,?_⟩
  · intro U large
    change product A D U + product B C U = 0
    rw [product_degree A D dA dD U large,product_degree B C dB dC U large,add_zero]
  · intro x
    unfold eval
    rw [Finset.sum_add_distrib]
    change eval (product A D) (support x)+eval (product B C) (support x)=_
    rw [product_eval,product_eval,hA,hB,hC,hD]
    rfl

theorem independent_span_hit (S : Finset (Vec J)) {a b c d : Vec J → F}
    (qa : Quadratic a) (qb : Quadratic b) (qc : Quadratic c) (qd : Quadratic d)
    (hit : ∃ x∈affineSpan F (S:Set (Vec J)),independent a b c d x) :
    ∃ l : List (Vec J),(∀ x∈l,x∈S) ∧ (l.length=1 ∨ l.length=3 ∨ l.length=5) ∧
      l.sum∈affineSpan F (S:Set (Vec J)) ∧ independent a b c d l.sum := by
  obtain ⟨p,deg,rep⟩ := quartic_score qa qb qc qd
  obtain ⟨x,hx,ind⟩ := hit
  obtain ⟨l,mem,len,span,found⟩ := quartic_span_hit S p deg
    ⟨x,hx,by rw [rep]; exact (score_ne_iff _ _ _ _ _).mpr ind⟩
  exact ⟨l,mem,len,span,(score_ne_iff _ _ _ _ _).mp (by rwa [rep] at found)⟩
#print axioms quartic_score
#print axioms independent_span_hit
end ExactPlaneDeterminant
