import Research.CrownIndexedOrReads

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds

/-- Gate indices of all OR gates, independent of the input. -/
def staticOrIds : (gs : List Gate) → Finset (Fin gs.length)
  | [] => ∅
  | g::gs =>
    let tail := (staticOrIds gs).map (Fin.succEmb _)
    if isOrGate g then insert 0 tail else tail

theorem staticOrIds_card (gs : List Gate) :
    (staticOrIds gs).card = (gs.filter isOrGate).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have h0 : (0 : Fin (gs.length+1)) ∉ (staticOrIds gs).map (Fin.succEmb _) := by simp
    cases h : isOrGate g <;> simp [staticOrIds,h,h0,ih]

theorem staticOrIds_reads (gs : List Gate) (n : ℕ) (i : Fin gs.length) (hi : i ∈ staticOrIds gs) :
    readAt gs n i.val ∈ orInputSets gs n := by
  induction gs generalizing n with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    refine Fin.cases ?_ (fun j => ?_) i hi
    · intro h0
      by_cases ho : isOrGate g = true
      · simp [readAt,orReads,orInputSets,ho]
      · simp [staticOrIds,ho] at h0
    · intro hj
      have tail : j ∈ staticOrIds gs := by
        by_cases ho : isOrGate g = true <;> simpa [staticOrIds,ho] using hj
      have mem := ih (n+1) j tail
      by_cases ho : isOrGate g = true <;> simp [orInputSets,readAt,ho,mem]

end PEqualNP.Research.MissingCell
