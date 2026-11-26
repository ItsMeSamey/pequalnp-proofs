import ExactPlaneActivationSlice
import ExactPlaneDeterminant
namespace ExactPlaneActiveDeterminant
open ExactPlaneAffineSpanHit ExactPlaneAffineSubstitution ExactPlaneActivationSlice ExactPlaneDeterminant
variable {J K : Type*} [Fintype J] [DecidableEq J]

theorem active_span (seed : Finset (Vec J)) (read : K→Vec J →ₗ[F] F) (offset target : K→F)
    {a b c d : Vec J→F} (qa : Quadratic a) (qb : Quadratic b) (qc : Quadratic c) (qd : Quadratic d)
    (hit : ∃ x∈affineSpan F (slice seed read offset target:Set (Vec J)),independent a b c d x) :
    ∃ l : List (Vec J),(∀ x∈l,x∈seed ∧ Active read offset target x) ∧
      (l.length=1 ∨ l.length=3 ∨ l.length=5) ∧
      l.sum∈affineSpan F (slice seed read offset target:Set (Vec J)) ∧
      Active read offset target l.sum ∧ independent a b c d l.sum := by
  classical
  obtain ⟨l,inside,len,sp,ok⟩ := independent_span_hit _ qa qb qc qd hit
  refine ⟨l,fun x hx => Finset.mem_filter.mp (inside x hx),len,sp,?_,ok⟩
  exact span_active read offset target _ (fun x hx => (Finset.mem_filter.mp hx).2) sp

/-- A domain-level witness transfers when the active part of the domain is
covered. The result belongs to the domain when the active seed span lies
there too, as it does for the whole activation slice. -/
theorem covered_domain (seed : Finset (Vec J)) (read : K→Vec J →ₗ[F] F) (offset target : K→F)
    (domain : Set (Vec J)) {a b c d : Vec J→F} (qa : Quadratic a) (qb : Quadratic b)
    (qc : Quadratic c) (qd : Quadratic d)
    (coverage : ∀ x∈domain,Active read offset target x →
      x∈affineSpan F (slice seed read offset target:Set (Vec J)))
    (inside : ∀ x∈affineSpan F (slice seed read offset target:Set (Vec J)),x∈domain)
    (hit : ∃ x∈domain,Active read offset target x ∧ independent a b c d x) :
    ∃ l : List (Vec J),(∀ x∈l,x∈seed ∧ Active read offset target x) ∧
      (l.length=1 ∨ l.length=3 ∨ l.length=5) ∧ l.sum∈domain ∧
      Active read offset target l.sum ∧ independent a b c d l.sum := by
  obtain ⟨l,hl,len,sp,active,ok⟩ := active_span seed read offset target qa qb qc qd
    (localize seed read offset target domain coverage hit)
  exact ⟨l,hl,len,inside _ sp,active,ok⟩
#print axioms active_span
#print axioms covered_domain
end ExactPlaneActiveDeterminant
