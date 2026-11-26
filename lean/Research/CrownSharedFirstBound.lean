import Research.CrownSharedFirstCompression
import Research.WegenerThreshold

namespace PEqualNP.Research.CrownIdentify
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Research.MissingCell

/-- On a minimal crown circuit with at most 23 ORs, at most three labels
can share a first firing OR between their row and column singleton inputs. -/
theorem shared_first_card_le_three (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) (mini : crownSizeMinimal C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (L : Finset (Fin 12)) (shared : ∀ i ∈ L, sharedFirst C i) : L.card ≤ 3 := by
  obtain ⟨D,dm,_,count,correct⟩ := compress_shared_first_labels C hm rep mini size ors L shared
  have lower := FreeAndNet.threshold_two_circuit_or_lower 12 D dm correct
  change 20 ≤ (D.gates.filter isOrGate).length at lower
  omega

end PEqualNP.Research.CrownIdentify
