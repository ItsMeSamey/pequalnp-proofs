import ThresholdSimpleIncidence
import ThresholdPeelSchedule
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ThresholdRegularSource
open ThresholdSimpleIncidence ThresholdPeelSchedule T2SoleOrSplice
namespace ThresholdStarTruth
def covered {n m} (ends : Fin n → Finset (Fin m)) (s : Finset (Fin n)) := s.biUnion ends

theorem covered_profile {C : Circuit} {n} (L : Layout C n) (s : Finset (Fin n)) :
    incidence (endpointLists L) (vector s)=List.ofFn (row (covered (endpoints L) s)) := by
  have bits (v : T2OrPartition.Id C) :
      (labels L v).any (fun j => (vector s).getD j false)=row (covered (endpoints L) s) v := by
    apply Bool.eq_iff_iff.mpr
    change _=true ↔ decide _=true
    rw [endpoint_profile,decide_eq_true_eq]
    exact Finset.mem_biUnion.symm
  simpa [incidence,endpointLists,labels,List.map_ofFn,Function.comp_def] using
    congrArg List.ofFn (funext bits)
end ThresholdStarTruth
