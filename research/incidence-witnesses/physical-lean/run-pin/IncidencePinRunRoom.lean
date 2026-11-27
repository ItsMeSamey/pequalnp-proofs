import IncidenceRunPinPhysical
import IncidencePinPlaneGeometry
namespace IncidencePinRunRoom
open SparseIncidence CircuitRewire IncidenceStartNormalization IncidenceHoistReaders IncidenceHoistWalk
open IncidenceHoistPrefix IncidenceHoistSparse IncidenceHoistPrune IncidenceRunPinPhysical
open IncidencePinPlaneGeometry IncidenceRobust
variable {q n : Nat} (C : Circuit n) (I : Fin n→Fin n→Prop) [DecidableRel I]

theorem room (bin : binary C) (live : Live C) (andL : soleAnd C n) (neg : negatives C I n 2)
    (pos : flags C I) (P Q : Finset (Fin n)) (hasPoint : ∀ l,∃ p,I p l)
    (hasLine : ∀ p,∃ l,I p l) (available : ∀ x∈Q, ∃ p∉P,I p x)
    (survives : ∃p∉P,∃l∉Q,I p l) :
    ∃ D : Circuit n, binary D ∧ Live D ∧
      D.size+2*(P.card+Q.card)+(IncidencePhysicalPinExpectation.forced C P).card≤C.size+P.card ∧
      (lower P Q ⁻¹' C.wire C.output) ⊆ D.wire D.output ∧
      D.wire D.output ⊆ (upper P Q ⁻¹' C.wire C.output) := by
  obtain ⟨on,off⟩ := witnesses C I pos neg P Q survives
  obtain ⟨D,bD,d,lo,hi⟩ := residual C bin P Q on off
  obtain ⟨E,e,bE,liveE,out,_⟩ := prune D bD
  have ledger := IncidencePinCompensation.raw_budget C I bin live andL neg pos P Q hasPoint hasLine available survives
  exact ⟨E,bE,liveE,by omega,out ▸ lo,out ▸ hi⟩

theorem existence (degree : ∀ l,Fintype.card {p // I p l}=q+1)
    (unique : ∀ a b,a≠b → ∃! l,I a l ∧ I b l) (hq : 0<q) (hn : n=q^2+q+1)
    (P : Finset (Fin n)) (small : P.card<q+1) (free : (removedLines I P).card<n) :
    (∀ l,∃ p,I p l) ∧ (∀ p,∃ l,I p l) ∧
      (∀ x∈removedLines I P, ∃ p∉P,I p x) ∧ (∃p∉P,∃l∉removedLines I P,I p l) := by
  have ex (l : Fin n) := survivor_on_line I degree P small l
  have line (p : Fin n) : ∃ l,I p l := by
    obtain ⟨l,hl⟩ := Finset.card_pos.mp (show 0<(lines I p).card by rw [lines_card I degree unique hq hn]; omega)
    exact ⟨l,(Finset.mem_filter.mp hl).2⟩
  have proper : ¬ Finset.univ ⊆ removedLines I P := by
    intro h
    have h' := Finset.card_le_card h
    simp at h'
    omega
  obtain ⟨l,_,fl⟩ := Finset.not_subset.mp proper
  obtain ⟨p,fp,inc⟩ := ex l
  exact ⟨fun t => (ex t).imp (fun _ h => h.2),line,fun t _ => ex t,⟨p,fp,l,fl,inc⟩⟩
#print axioms room
end IncidencePinRunRoom
