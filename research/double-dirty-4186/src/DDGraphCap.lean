import DDCapRealization
import DDIndexedIsolation
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed

theorem cap_realization {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (s : OriginalCut G C) : Nonempty (CapRealization s) := by
  apply cap_of_isolation s
  intro z A B W
  dsimp only
  intro ha hb hw
  let p := splitCuts n C (orT G C) s.mixer
  let a : Fin (n+rank n C p C.size) := ⟨A.2,ref_bound ha⟩
  let b : Fin (n+rank n C p C.size) := ⟨B.2,ref_bound hb⟩
  let w : Fin (n+rank n C p C.size) := ⟨W.2,ref_bound hw⟩
  have iso := cap_apart s.edge s.least s.form z a b w A.1 B.1 W.1 ha hb hw
  have zt := z.onlyAffected s.top (Finset.mem_filter.mp s.centrelessTop).1 s.influence
  simpa only [zt] using iso

theorem virtual_evidence {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (s : OriginalCut G C) : s.VirtualEvidence :=
  (cap_realization s).elim (fun cap => cap.virtualEvidence)
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
