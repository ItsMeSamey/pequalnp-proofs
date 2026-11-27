import IncidencePhysicalZeroFlow
import IncidenceHoistPrune
import IncidenceHoistReaders
namespace IncidencePinLowLedger
open scoped BigOperators
open CircuitRewire IncidenceStartNormalization IncidenceHoistReaders IncidenceHoistPrune
open IncidenceOperandLedger
variable {n : Nat}

theorem fan_uses (C : Circuit n) (i : Nat) : fan C.code C.size i=(IncidenceStartNormalization.uses C i : Int) := by
  unfold fan IncidenceStartNormalization.uses
  generalize C.size = t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ,List.range_succ,List.map_append,List.sum_append]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_add,ih]
    by_cases l : (C.code t).left=i <;> by_cases r : (C.code t).right=i <;> simp [occ,l,r]

theorem ancestor_port {C : Circuit n} {w : Nat} (h : Anc C w) (ne : w≠C.output) :
    0<IncidenceStartNormalization.uses C w := by
  have mem (i j : Nat) (b : Bool) (hj : j<C.size) (read : operand (C.code j) b=i) :
      0<IncidenceStartNormalization.uses C i := by
    rw [← occurrence_count]
    exact List.length_pos_of_mem ((occurrence_mem C i j b).mpr ⟨hj,read⟩)
  cases h with
  | output => contradiction
  | left j h _ => exact mem _ j true h rfl
  | right j h _ => exact mem _ j false h rfl

def deadRaw (C : Circuit n) (z : Nat→Bool) := (Finset.range (n+n)).filter (fun i => z i=true)
def charged (C : Circuit n) (z : Nat→Bool) :=
  (Finset.range C.size).filter (fun j => z (C.code j).left || z (C.code j).right)

theorem low_count (C : Circuit n) (z : Nat→Bool) :
    ((charged C z).card : Int)=∑j∈Finset.range C.size,removed z (C.code j) := by
  classical
  unfold charged
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  simp [removed,bit]

theorem budget (C : Circuit n) (z : Nat→Bool) (pins : Finset Nat)
    (bin : binary C) (live : Live C) (out : z C.output=false)
    (eval : ∀ j<C.size,z (n+n+j)=zeroAt z (C.code j))
    (raw : ∀ i∈deadRaw C z,0<IncidenceStartNormalization.uses C i)
    (credit : ∀ i∈deadRaw C z,i∉pins → IncidenceStartNormalization.uses C i=1 →
      ∃ j<C.size, (C.code j).op=.meet ∧ z (C.code j).left≠z (C.code j).right ∧
        (if z (C.code j).left then (C.code j).left else (C.code j).right)=i) :
    2*(deadRaw C z).card ≤ (charged C z).card+pins.card := by
  classical
  let D := deadRaw C z
  let S := D.filter (fun i => IncidenceStartNormalization.uses C i=1)
  let U := S \ pins
  let paid := (Finset.range C.size).filter (fun j => (C.code j).op=.meet ∧
    z (C.code j).left≠z (C.code j).right)
  have debt : (2:Int)*D.card ≤ (∑ w∈D,fan C.code C.size w)+S.card := by
    have lower (w : Nat) (hw : w∈D) :
        (2:Int) ≤ fan C.code C.size w + (if IncidenceStartNormalization.uses C w=1 then 1 else 0) := by
      rw [fan_uses]
      have := raw w hw
      split <;> omega
    have bound := Finset.sum_le_sum lower
    rw [Finset.sum_add_distrib] at bound
    have count : (S.card:Int)=∑ w∈D, if IncidenceStartNormalization.uses C w=1 then (1:Int) else 0 := by
      rw [show S=(D.filter (fun i => IncidenceStartNormalization.uses C i=1)) from rfl, Finset.card_filter]
      push_cast <;> rfl
    simpa [←count,mul_comm] using bound
  have sBound : S.card ≤ pins.card + U.card := by
    have h : S⊆pins∪U := by
      intro i hi
      by_cases p : i∈pins
      · exact Finset.mem_union_left _ p
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi,p⟩)
    exact (Finset.card_le_card h).trans (Finset.card_union_le ..)
  have charge (w : ↥U) := credit w.val (Finset.mem_filter.mp (Finset.mem_sdiff.mp w.property).1).1
    (Finset.mem_sdiff.mp w.property).2 (Finset.mem_filter.mp (Finset.mem_sdiff.mp w.property).1).2
  let f (w : ↥U) : ↥paid :=
    ⟨(charge w).choose,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (charge w).choose_spec.1,
      (charge w).choose_spec.2.1,(charge w).choose_spec.2.2.1⟩⟩
  have fInj : Function.Injective f := by
    intro a b h
    have eq := congrArg Subtype.val h
    change (charge a).choose=(charge b).choose at eq
    apply Subtype.ext
    calc
      a.val = _ := (charge a).choose_spec.2.2.2.symm
      _ = _ := congrArg (fun j => if z (C.code j).left then (C.code j).left else (C.code j).right) eq
      _ = b.val := (charge b).choose_spec.2.2.2
  have paidBound : U.card≤paid.card := by simpa using Fintype.card_le_of_injective f fInj
  have credits : (paid.card:Int)=∑j∈Finset.range C.size, oneAnd z (C.code j) := by
    unfold paid
    rw [Finset.card_filter]
    push_cast <;> rfl
  have rawSum : (∑ w∈D,fan C.code C.size w)=
      ∑w∈Finset.range (n+n),fan C.code C.size w*bit (z w) := by
    simp [D,deadRaw,Finset.sum_filter,bit,mul_ite]
  have balance := literal_ledger C.code z (n+n) C.size
    (fun j hj => ⟨(C.earlier j hj).1.trans_le (by omega),(C.earlier j hj).2.trans_le (by omega)⟩) bin eval
  have surplus : 0 ≤ ∑j∈Finset.range C.size,(fan C.code C.size (n+n+j)-1)*bit (z (n+n+j)) := by
    apply Finset.sum_nonneg
    intro j hj
    cases mark : z (n+n+j) with
    | false => simp [bit]
    | true =>
      have ne : n+n+j≠C.output := by intro e; rw [e,out] at mark; contradiction
      have pos := ancestor_port (live j (Finset.mem_range.mp hj)) ne
      rw [fan_uses]
      simp only [bit,ite_true,mul_one]
      omega
  rw [←low_count,←rawSum,←credits] at balance
  change 2*D.card ≤ _+_
  omega

#print axioms budget
end IncidencePinLowLedger
