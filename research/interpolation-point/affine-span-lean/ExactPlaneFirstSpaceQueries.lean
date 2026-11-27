import ExactPlaneFirstRelation
import ExactPlaneFirstSpaceRecovery

namespace ExactPlaneFirstSpaceQueries
open ExactPlaneFirstRelation ExactPlanePhysicalConverse
open scoped BigOperators
variable {N : ℕ} {K B : Type*} [AddCommGroup K] [Module F K] [AddCommGroup B] [Module F B]

structure ScalarContract (k : Fin N→K) (b : Fin N→B)
    (q : (Fin N→F)→Option (Finset (Fin N))) : Prop where
  safe : ∀ s,q s=none → ¬∃ A,ExactTrace k b s A
  witness : ∀ s U,q s=some U → ∃ g,Match g k b U ∧ (∑ i∈U,k i)=0 ∧ (∑ i∈U,s i)=1

noncomputable def weights (f : ExactPlaneFirstSpaceRecovery.Probe N) : Fin N→F :=
  Classical.choose (charge_rep f)

theorem contract {k : Fin N→K} {b : Fin N→B} {q} (ok : ScalarContract k b q) :
    ExactPlaneFirstSpaceRecovery.Contract (first k b) mask (fun f => q (weights f)) := by
  constructor
  · intro f none
    have rep : charge (weights f)=f := Classical.choose_spec (charge_rep f)
    have incl : first k b ≤ LinearMap.ker (charge (weights f)) := by
      by_contra bad
      exact ok.safe _ none ((scalar_iff_trace k b _).mp bad)
    rw [←rep]
    exact ((first k b).mem_dualAnnihilator _).mpr (fun _ hx=>incl hx)
  · intro f U someU
    obtain ⟨g,matched,key,one⟩ := ok.witness _ U someU
    have rel := (mem_relation k b g (mask U)).mpr ⟨by simpa only [aggregate_support,support_mask] using key,
      by simpa only [support_mask] using matched⟩
    have rep : charge (weights f)=f := Classical.choose_spec (charge_rep f)
    refine ⟨(show relation k b g ≤ first k b from le_iSup _ g) rel,?_⟩
    rw [←rep]
    have h : charge (weights f) (mask U)=1 := by simpa only [charge,aggregate_support,support_mask] using one
    rw [h]
    exact one_ne_zero

#print axioms contract
end ExactPlaneFirstSpaceQueries
