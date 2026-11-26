import ExactPlaneOntoReadSpan
import ExactPlaneConcreteSampler
namespace ExactPlaneLookupDeterminant
open ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit ExactPlaneActivationSlice ExactPlaneDeterminant
universe u

/-- A single seed population works for all feasible systems of at most r
affine equations and all four residual coordinates, including dimension zero. -/
theorem universal_read_seed (m r : ℕ) :
    ∃ seed : Finset (Vec (Fin m)),seed.card≤max 1 ((2*m*2^(r+1))^2) ∧
      ∀ k≤r,∀ (read : Fin k→Vec (Fin m) →ₗ[F] F) (offset target : Fin k→F),
      ∀ (K : Type u) [Fintype K], ∀ a b c d : Residual (Fin m) K,
      (∃ x,Active read offset target x ∧ independent a.read b.read c.read d.read x) →
      ∃ l : List (Vec (Fin m)), (∀ x∈l,x∈seed ∧ Active read offset target x) ∧
        (l.length=1 ∨ l.length=3 ∨ l.length=5) ∧
        l.sum∈affineSpan F (slice seed read offset target:Set (Vec (Fin m))) ∧
        Active read offset target l.sum ∧ independent a.read b.read c.read d.read l.sum := by
  obtain ⟨seed,cap,sampler⟩ := ExactPlaneConcreteSampler.all_dimensions m (r+1)
  exact ⟨seed,cap,fun k hk read offset target K inst a b c d hit =>
    onto_sampled_read_span seed r sampler k hk read offset target a b c d hit⟩
#print axioms universal_read_seed
end ExactPlaneLookupDeterminant
