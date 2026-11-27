import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Elim
import PEqualNP.MetaComplexity.Helpers.ExactMaj3

namespace BullLeast4186

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity.Helpers
open PEqualNP.TopForm

abbrev bull : SimpleGraph (Fin 5) :=
  PEqualNP.EdgeOwnership.edgeGraph 5 [(0, 1), (0, 2), (0, 4), (1, 2), (1, 3)]

private def full : (Fin 5 → Bool) → Bool := graphFun bull ∅
private def paw (x : Fin 4 → Bool) := full (Fin.snoc x false)
private def triangle (x : Fin 3 → Bool) := paw (Fin.snoc x false)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem lower (C : Circuit) (hAO : IsAO2 5 C)
    (hfun : circuitFun 5 C = graphFun bull ∅) : 6 ≤ C.size := by
  by_contra! small
  have h5 : HasCircuitSize 5 full 5 := by
    refine ⟨C, ?_, by omega, fun x => congrFun hfun x⟩
    intro g hg
    refine ⟨?_, (hAO.2.2 g hg).le⟩
    rcases hAO.1 g hg with h | h <;> simp [h]
  have h4 : HasCircuitSize 4 paw 4 := by
    apply gate_elim 4 full false 4 _ _ h5
    · exact ⟨fun i => decide (i = 0), by decide +kernel⟩
    · exact ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), by decide +kernel⟩
  have h3 : HasCircuitSize 3 triangle 3 := by
    apply gate_elim 3 paw false 3 _ _ h4
    · exact ⟨fun i => decide (i = 1), by decide +kernel⟩
    · exact ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), by decide +kernel⟩
  have heq : triangle = ExactMaj3.maj3 := by
    funext x
    exact (by decide +kernel : ∀ y : Fin 3 → Bool, triangle y = ExactMaj3.maj3 y) x
  exact ExactMaj3.maj3_lower (heq ▸ h3)

private def dirtyCircuit : Circuit := ⟨[⟨.or,[0,3]⟩, ⟨.or,[1,4]⟩, ⟨.and,[5,6]⟩,
    ⟨.or,[7,2]⟩, ⟨.or,[0,1]⟩, ⟨.and,[8,9]⟩], 10⟩

theorem dirtyLeast : IsLeastAO bull dirtyCircuit := by
  have compute : circuitFun 5 dirtyCircuit = graphFun bull ∅ := by
    funext x
    exact (by decide +kernel : ∀ y : Fin 5 → Bool, circuitFun 5 dirtyCircuit y = graphFun bull ∅ y) x
  exact ⟨by decide +kernel, compute, fun D hD hf => lower D hD hf⟩

end BullLeast4186
