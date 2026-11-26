import ThresholdOrRaw
import ThresholdOrBranch
open PEqualNP.CircuitLowerBounds ThresholdOrGroups
namespace ThresholdOrExtraction

def earlyPorts (C : Circuit) (k : Nat) (i : T2OrPartition.Id C) :=
  (C.gates.get i).inputs.countP (fun w => decide (w<k))

theorem split_port (xs : List Nat) (k : Nat) :
    xs.countP (fun w => decide (w<k+1)) =
      xs.countP (fun w => decide (w<k)) + (xs.filter (· == k)).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Nat.lt_succ_iff] at ih
    rcases lt_trichotomy x k with lt|eq|gt
    · have lt' : x<k+1 := by omega
      simp [List.countP_cons,lt,lt',le_of_lt lt,ne_of_lt lt,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · subst x
      simp [List.countP_cons,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · have ne := ne_of_gt gt
      have nl : ¬ x<k := by omega
      have nl' : ¬ x<k+1 := by omega
      simp [List.countP_cons,nl,nl',not_le_of_gt gt,ne,ih]

theorem list_charge (C : Circuit) (k : Nat) (xs : List (T2OrPartition.Id C)) :
    (xs.map (earlyPorts C (k+1))).sum = (xs.map (earlyPorts C k)).sum +
      (xs.flatMap (fun i => ((C.gates.get i).inputs.filter (· == k)).map (fun _ => i))).length := by
  induction xs with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append,List.length_map,earlyPorts] at *
    rw [split_port,ih]; omega

theorem regular_total (C : Circuit) (k : Nat)
    (twice : ∀ w<k, (T2OrPartition.readers C w).length=2) :
    ((List.finRange C.gates.length).map (earlyPorts C k)).sum = 2*k := by
  induction k with
  | zero =>
    have emp : earlyPorts C 0 = fun _ => 0 := by
      funext i
      simp [earlyPorts]
    rw [emp]
    simp
  | succ k ih =>
    rw [list_charge]
    change _ + (T2OrPartition.readers C k).length=_
    rw [ih (fun w h => twice w (by omega)),twice k (by omega)]
    omega

theorem raw_count_two {C : Circuit} {n : Nat} (layout : Layout C n)
    (reg : MeetsInternal layout) (pin : T2OrPartition.Id C → Nat)
    (twice : ∀ w<n, (T2OrPartition.readers C w).length=2) :
    rawCount (forest layout pin) = 2*n := by
  have charge (i : T2OrPartition.Id C) : ports C n (n+i.val)=earlyPorts C n i := by
    simp [ports,earlyPorts]
  have vanish (i : T2OrPartition.Id C) (op : layout.op i ≠ .or) : earlyPorts C n i=0 := by
    have oa : layout.op i=.and := by cases e : layout.op i <;> simp_all
    have h := reg i oa
    have ins := layout_inputs (layout.atIndex i)
    unfold earlyPorts
    rw [ins]
    simp [List.countP_cons,not_lt.mpr h.1,not_lt.mpr h.2]
  have filt (xs : List (T2OrPartition.Id C)) :
      (((xs.filter (fun i => decide (layout.op i=.or))).map (fun i => n+i.val)).map (ports C n)).sum =
      (xs.map (earlyPorts C n)).sum := by
    induction xs with
    | nil => rfl
    | cons i is ih =>
      simp only [List.map_map] at ih
      by_cases e : layout.op i=.or
      · simp [e,charge,ih]
      · simp [e,vanish i e,ih]
  exact (physical_raw_total layout pin).trans ((filt _).trans (regular_total C n twice))

#print axioms raw_count_two
end ThresholdOrExtraction
