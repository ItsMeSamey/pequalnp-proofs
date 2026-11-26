import ThresholdCoveredPins
import ThresholdEdgeRows
import ThresholdEdgeRealization
namespace ThresholdSimpleIncidence
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ThresholdRegularSource
open ThresholdPeelSchedule ThresholdStarTruth T2SoleOrSplice

theorem physical_rows {C : Circuit} {n} (L : Layout C n) (D : Circuit)
    (rep : ∀ s : Finset (Fin n), D.eval (incidence (endpointLists L) (vector s))=true ↔ 2≤s.card) :
    EdgeRows (endpoints L) (fun s => D.eval (List.ofFn (row s))) := by
  have eval (s : Finset (Fin n)) := rep s
  simp only [covered_profile] at eval
  constructor
  · intro e
    have reject : ¬ D.eval (List.ofFn (row (covered (endpoints L) {e})))=true :=
      fun yes => by simpa using (eval {e}).mp yes
    simpa [covered] using Bool.eq_false_iff.mpr reject
  · intro e d ne
    have yes := (eval {e,d}).mpr (by simp [ne])
    simpa [covered] using yes
end ThresholdSimpleIncidence
