import ThresholdProbeOrder
import ThresholdSharedPartition
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ResidualSurplus
open ThresholdFanoutBudget ThresholdSharedFlow ThresholdSharedPartition
namespace ThresholdSecondaryReceivers
def ports (C : Circuit) (n : Nat) (u : Id C) : List (Id C) :=
  (readers C (n+u.val)).map (owner C n)
def signature (C : Circuit) (n : Nat) (u : Id C) := (ports C n u).toFinset
def good (C : Circuit) (n : Nat) (H : Finset (Id C)) := H.filter (fun u =>
  (readers C (n+u.val)).length=2 ∧ ∀ i∈readers C (n+u.val), isOr C i=true)
def receivers (C : Circuit) (n : Nat) (H : Finset (Id C)) :=
  (good C n H).biUnion (signature C n)
variable {C : Circuit} {n : Nat} (L : Layout C n)
theorem or_carry {u i : Id C} {w : Nat} (pin : w∈(C.gates.get i).inputs)
    (kind : isOr C i=true) (onwire : on L u w=true) : active L u i=true := by
  rw [row_eq]
  by_cases iu : i=u
  · simp [iu]
  rw [if_neg iu,(physical_op L i).mp kind]
  rw [layout_inputs (L.atIndex i)] at pin
  rcases List.mem_cons.mp pin with eq|tail
  · simp [←eq,onwire]
  · have eq := List.mem_singleton.mp tail
    simp [←eq,onwire]

theorem owner_carry (u i : Id C) (hot : active L u i=true) :
    active L u (owner C n i)=true := by
  cases e : next C n i with
  | none => simpa [owner_of_stop C n i e] using hot
  | some j =>
    rw [owner_of_next C n i j e]
    have pin : j.val∈readers C (n+i.val) := by simp [next_readers e]
    exact owner_carry u j.val (or_carry L (reader_pin pin) (next_is_or e).2 hot)
termination_by C.gates.length-i.val
decreasing_by have hj := j.val.isLt; have lt := j.property; change i.val<j.val.val at lt; omega

theorem receiver_later {H : Finset (Id C)} {u r : Id C} (hu : u∈good C n H)
    (mem : r∈signature C n u) : u<r ∧ active L u r=true := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp mem)
  have pin := reader_pin hi
  have own : active L u u=true := by simp [row_eq]
  have spec := (Finset.mem_filter.mp hu).2
  have hot := owner_carry L u i (or_carry L pin (spec.2 i hi) own)
  have top := L.atIndex i
  rw [layout_inputs top] at pin
  have hl := top.leftEarlier
  have hr := top.rightEarlier
  have before : u < i := by
    change u.val < i.val
    simp only [List.mem_cons,List.not_mem_nil,or_false] at pin
    rcases pin with h|h <;> omega
  exact ⟨lt_of_lt_of_le before (owner_spec C n i).1,hot⟩
end ThresholdSecondaryReceivers
