import IncidencePinCompensation
import IncidenceRunPinCompile
namespace IncidencePinLosses
open IncidenceStartNormalization IncidencePinLowLedger IncidencePinCompensation IncidenceRunPinCompile
variable {n : Nat}

noncomputable def physical (C : Circuit n) (P : Finset (Fin n)) : Finset Nat :=
  (IncidencePhysicalPinExpectation.forced C P).map Fin.valEmbedding

noncomputable def force (C : Circuit n) (P : Finset (Fin n)) (j : Nat) : Bool := by
  classical exact decide (j∈physical C P)

theorem force_iff (C : Circuit n) (P : Finset (Fin n)) (j : Nat) (hj : j<C.size) :
    force C P j=true ↔ (⟨j,hj⟩ : Fin C.size)∈IncidencePhysicalPinExpectation.forced C P := by
  classical
  simp only [force,decide_eq_true_eq,physical,Finset.mem_map]
  constructor
  · rintro ⟨a,h,e⟩
    exact (Fin.ext e : a=⟨j,hj⟩) ▸ h
  · exact fun h => ⟨_,h,rfl⟩

theorem charge_filter (code : Nat→CircuitRewire.Gate) (z force : Nat→Bool) (s : Nat) :
    charges code z force s=((Finset.range s).filter (fun j=> loss code z force j=true)).card := by
  induction s with
  | zero => simp [charges]
  | succ s ih =>
    rw [charges,ih,Finset.range_add_one,Finset.filter_insert]
    cases flag : loss code z force s <;> simp [flag,Finset.card_insert_of_notMem]

theorem separate_loss (C : Circuit n) (P Q : Finset (Fin n)) :
    charges C.code (z C P Q) (force C P) C.size =
      (charged C (z C P Q)).card+(IncidencePhysicalPinExpectation.forced C P).card := by
  classical
  let marked := charged C (z C P Q)
  let F := physical C P
  have bounded (j : Nat) (h : j∈F) : j<C.size := by
    obtain ⟨g,_,e⟩ := Finset.mem_map.mp h
    exact e ▸ g.isLt
  have sets : ((Finset.range C.size).filter (fun j=> loss C.code (z C P Q) (force C P) j=true))=marked∪F := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,loss,Bool.or_eq_true,
      force,decide_eq_true_eq,marked,charged,F]
    constructor
    · rintro ⟨a,b|c⟩
      · exact Or.inl ⟨a,b⟩
      · exact Or.inr c
    · rintro (⟨a,b⟩|c)
      · exact ⟨a,Or.inl b⟩
      · exact ⟨bounded j c,Or.inr c⟩
  have dis : Disjoint marked F := by
    apply Finset.disjoint_left.mpr
    intro j hl hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_map.mp hf
    exact forced_separate C P Q g hg hl
  rw [charge_filter,sets,Finset.card_union_of_disjoint dis]
  simp [F,physical,marked]

#print axioms separate_loss
end IncidencePinLosses
