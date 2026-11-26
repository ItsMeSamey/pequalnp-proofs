import ExactPlaneDeterminant
import ExactPlaneTwoBitLookup
namespace ExactPlaneLookupDeterminant
open ExactPlaneSubsetPolynomial ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit ExactPlaneDeterminant
open scoped BigOperators

structure Bit (J : Type*) where
  constant : F
  weight : J → F

structure Residual (J K : Type*) where
  base : Bit J
  left : K → Bit J
  right : K → Bit J
  table : K → F × F → F
  weight : K → F

variable {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K]
noncomputable def Bit.read (b : Bit J) (u : Vec J) : F :=
  b.constant+∑ i∈support u,b.weight i
noncomputable def Residual.read (r : Residual J K) (u : Vec J) : F :=
  r.base.read u+∑ k,r.weight k*r.table k ((r.left k).read u,(r.right k).read u)

theorem residual_quadratic (r : Residual J K) : Quadratic r.read := by
  obtain ⟨p,dp,agree⟩ := ExactPlaneTwoBitLookup.lookup_sum
    (affineRow r.base.constant r.base.weight) (affineRow_degree _ _)
    (fun k v => r.weight k*r.table k v)
    (fun k => affineRow (r.left k).constant (r.left k).weight)
    (fun k => affineRow (r.right k).constant (r.right k).weight)
    (fun k => affineRow_degree _ _) (fun k => affineRow_degree _ _)
  exact ⟨p,dp,fun u => by simpa only [Residual.read,Bit.read,affineRow_eval] using agree (support u)⟩

theorem determinant_quartic (a b c d : Residual J K) :
    ∃ p : Coeff J, degreeLE 4 p ∧ ∀ x,eval p (support x)=score a.read b.read c.read d.read x :=
  quartic_score (residual_quadratic a) (residual_quadratic b) (residual_quadratic c) (residual_quadratic d)

theorem same_span (S : Finset (Vec J)) (a b c d : Residual J K)
    (hit : ∃ x∈affineSpan F (S:Set (Vec J)),independent a.read b.read c.read d.read x) :
    ∃ l : List (Vec J),(∀ x∈l,x∈S) ∧ (l.length=1 ∨ l.length=3 ∨ l.length=5) ∧
      l.sum∈affineSpan F (S:Set (Vec J)) ∧ independent a.read b.read c.read d.read l.sum :=
  independent_span_hit S (residual_quadratic a) (residual_quadratic b)
    (residual_quadratic c) (residual_quadratic d) hit
#print axioms determinant_quartic
#print axioms same_span
end ExactPlaneLookupDeterminant
