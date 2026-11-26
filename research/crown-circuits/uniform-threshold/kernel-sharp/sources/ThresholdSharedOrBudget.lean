import ThresholdFanoutBudget

namespace ThresholdSharedOrBudget
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2CubeDeletion
open ThresholdRegularSource T2RegularOrDelete ThresholdFanoutBudget T2OrPartition

def sharedGates (C : Circuit) (n : Nat) :=
  (List.finRange C.gates.length).filter (fun i => decide (2 ≤ (readers C (n+i.val)).length))

/-- Includes shared OR roots with no raw operands. -/
def sharedOrs (C : Circuit) (n : Nat) := (sharedGates C n).filter (isOr C)

theorem shared_stops {C : Circuit} {n : Nat} {i : Id C} (hi : i∈sharedGates C n) :
    T2OrPartition.next C n i=none := by
  have h : 2 ≤ (readers C (n+i.val)).length := by simpa using (List.mem_filter.mp hi).2
  cases e : T2OrPartition.next C n i with
  | none => rfl
  | some j => simp [next_readers e] at h

theorem regular_shared_budget {n out : Nat} {gs : List Raw}
    (M : LexMinimum n (source gs out)) (reg : Regular n gs) :
    (sharedOrs (source gs out) n).length + 2*n ≤ (source gs out).size + 1 := by
  let C := source gs out
  let L := layout n gs out M.eligible
  let f := fun i : Id C => (readers C (n+i.val)).length
  let obs := fun i : Id C => decide (C.output=n+i.val)
  let xs := List.finRange C.gates.length
  have live (i : Id C) (_ : i ∈ xs) (h : obs i=false) : 1 ≤ f i :=
    live_slots L M i (by simpa [obs] using h)
  have h := mandatory_and_shared xs f obs live
  have len : xs.length=C.gates.length := List.length_finRange
  rw [len] at h
  change C.gates.length + (sharedGates C n).length ≤ (xs.map f).sum + (xs.filter obs).length at h
  have one : (xs.filter obs).length ≤ 1 := output_unique C n
  have balance : (xs.map f).sum + 2*n = 2*C.gates.length :=
    balance_slots L (regular_inputs n gs out M.eligible reg).2.1
  have sub : (sharedOrs C n).length ≤ (sharedGates C n).length :=
    List.length_filter_le _ _
  change (sharedOrs C n).length + 2*n ≤ C.gates.length + 1
  omega

#print axioms regular_shared_budget
end ThresholdSharedOrBudget
