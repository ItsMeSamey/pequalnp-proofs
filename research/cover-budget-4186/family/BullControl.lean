import PEqualNP.Defs

namespace BullControl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

abbrev G := edgeGraph 5 [(0,2), (0,3), (1,2), (0,4), (2,4)]
def C : Circuit := ⟨[⟨.or,[0,1]⟩, ⟨.or,[2,3]⟩, ⟨.and,[5,6]⟩,
  ⟨.or,[7,4]⟩, ⟨.or,[0,2]⟩, ⟨.and,[8,9]⟩], 10⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem computes : circuitFun 5 C = graphFun G ∅ := by
  funext x
  exact (by decide +kernel : ∀ y : Fin 5 → Bool, circuitFun 5 C y = graphFun G ∅ y) x

theorem admissible : IsAO2 5 C ∧ C.size = 6 ∧ NoFourCycle G ∧ G.edgeFinset.Nonempty ∧
    PEqualNP.TopForm.TopForm G C := by decide +kernel

theorem classes : tops G C = {5} ∧ centreless G C = ∅ ∧ junk G C = {2} ∧
    orN G C = {0,1,3,4} ∧ lam G C = {4} := by decide +kernel

theorem uncovered : Ustar G C = {s(0,2), s(0,3), s(1,2)} := by decide +kernel

theorem coverUpper : CoverPromise.IsVertexCover G {0,2} ∧
    ({0,2} : Finset (Fin 5)).card = 2 := by
  unfold CoverPromise.IsVertexCover
  decide +kernel

theorem coverLower : ∀ S : Finset (Fin 5), CoverPromise.IsVertexCover G S → 2 ≤ S.card := by
  unfold CoverPromise.IsVertexCover
  decide +kernel

theorem tight : ({0,2} : Finset (Fin 5)).card + (Ustar G C).card =
    (tops G C \ centreless G C).card + 2 * (centreless G C).card +
    (junk G C).card + (orN G C \ lam G C).card := by decide +kernel

end BullControl
