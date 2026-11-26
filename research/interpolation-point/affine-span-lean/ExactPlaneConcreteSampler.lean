import ExactPlaneFieldCard
import ExactPlaneFieldSampler
import ExactPlaneSamplerRank
namespace ExactPlaneConcreteSampler
open ExactPlaneAffineSpanHit ExactPlaneSamplerRank ExactPlaneFieldSampler

/-- In dimension zero the ambient cube itself consists of one point, and
there is no need to choose an extension field. -/
theorem zero (R : Nat) :
    ∃ S : Finset (Vec (Fin 0)), S.card=1 ∧ OntoHits S R := by
  classical
  exact ⟨{0},by simp,zero_hits R⟩

/-- The field and its dual are counted at the same dimension. Distinct
parameter pairs are allowed to produce equal samples. -/
theorem positive (m R : Nat) (hm : 0<m) :
    ∃ S : Finset (Vec (Fin m)), S.card≤(2*m*2^R)^2 ∧ OntoHits S R := by
  classical
  let E := ExactPlaneFieldCard.K (m*2^R)
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype (E →ₗ[F] F) := Fintype.ofEquiv E
    (Module.finBasis F E).toDualEquiv.toEquiv
  obtain ⟨large,cost⟩ := ExactPlaneFieldCard.seed_bound m R hm
  exact ⟨seed E m,(seed_card_le E m).trans cost,field_hits m R E hm large⟩

theorem all_dimensions (m R : Nat) :
    ∃ S : Finset (Vec (Fin m)), S.card≤max 1 ((2*m*2^R)^2) ∧ OntoHits S R := by
  cases m with
  | zero =>
    obtain ⟨S,size,hit⟩ := zero R
    exact ⟨S,by simp [size],hit⟩
  | succ m =>
    obtain ⟨S,size,hit⟩ := positive (m+1) R (Nat.succ_pos _)
    exact ⟨S,size.trans (le_max_right _ _),hit⟩

#print axioms all_dimensions
end ExactPlaneConcreteSampler
