import ThresholdNamedIncidence
import ThresholdSecondaryReceivers
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ThresholdRegularSource ThresholdNamedIncidence
open private portWeight from ThresholdNamedIncidence
namespace ThresholdExternalCount
theorem branch_count (C : Circuit) (n : Nat) (u : T2OrPartition.Id C) (stop : T2OrPartition.next C n u=none) (p z : Nat) :
    let t := (branch C n p z).val
    t.exts.count (n+u.val) = (if z=n+u.val then 1 else 0) + (t.gates.map (weight C n (n+u.val))).sum := by
  rw [branch]
  split
  next small =>
    have h : z≠n+u.val := by omega
    simp [Tree.exts,Tree.gates,h]
  next large =>
    split
    next ex =>
      have ne : z≠n+u.val := by
        intro e
        obtain ⟨d,ed,⟨j,ej,_⟩,_⟩ := ex
        have same : d=u := Fin.ext (by omega)
        subst d; rw [stop] at ej; contradiction
      let h := ex.choose_spec.2.2
      let l := h.choose
      let r := h.choose_spec.choose
      have g : GateAt C n z .or l r := h.choose_spec.choose_spec
      have left := branch_count C n u stop z l
      have right := branch_count C n u stop z r
      simp only [Tree.exts,Tree.gates,List.count_append,List.map_cons,List.sum_cons,List.map_append,List.sum_append,ne,ite_false,zero_add]
      dsimp only at left right
      rw [left,right,portWeight g]
      dsimp only [l,r,h] at *
      omega
    next => by_cases e : z=n+u.val <;> simp [Tree.exts,Tree.gates,e,List.count_cons,eq_comm]
termination_by z
decreasing_by all_goals first | exact g.leftEarlier | exact g.rightEarlier

theorem block_count {C : Circuit} {n : Nat} (L : Layout C n) (u : T2OrPartition.Id C) (stop : T2OrPartition.next C n u=none)
    (only : ∀ i∈T2OrPartition.readers C (n+u.val), T2OrPartition.isOr C i=true)
    (pin : T2OrPartition.Id C → Nat) (i : T2OrPartition.Id C) :
    (makeBlock L pin i).exts.count (n+u.val) =
      ((makeBlock L pin i).orIDs.map (weight C n (n+u.val))).sum := by
  unfold makeBlock
  split
  · rename_i ea
    have no : n+u.val∉(C.gates.get i).inputs := fun hit => by
      have eo := (physical_op L i).mp (only i (T2OrPartition.read_mem hit)); simp [ea] at eo
    rw [layout_inputs (L.atIndex i)] at no
    simpa [Block.exts,Block.orIDs,List.count_eq_zero] using no
  · rename_i e
    let g : GateAt C n (n+i.val) .or (L.left i) (L.right i) := e ▸ L.atIndex i
    simp only [Block.exts,Block.orIDs,root,Tree.exts,Tree.gates,List.count_append,List.map_cons,
      List.map_append,List.sum_cons,List.sum_append]
    rw [branch_count C n u stop,branch_count C n u stop,portWeight g]
    omega

theorem point_count {C : Circuit} {n : Nat} (L : Layout C n) (u : T2OrPartition.Id C) (stop : T2OrPartition.next C n u=none)
    (only : ∀ i∈T2OrPartition.readers C (n+u.val), T2OrPartition.isOr C i=true) (pin : T2OrPartition.Id C → Nat) :
    ((forest L pin).map (fun b => b.exts.count (n+u.val))).sum = (T2OrPartition.readers C (n+u.val)).length := by
  have inv (xs : List (T2OrPartition.Id C)) :
      ((xs.map (makeBlock L pin)).map (fun b => b.exts.count (n+u.val))).sum =
        ((allGates (xs.map (makeBlock L pin))).map (weight C n (n+u.val))).sum := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      simp only [List.map_cons,List.sum_cons,allGates,List.flatMap_cons,List.map_append,List.sum_append,block_count L u stop only] at *
      exact congrArg (_+·) ih
  calc
    _ = _ := inv (fixed C n)
    _ = ((orIndex L).map (weight C n (n+u.val))).sum := ((ids_permute L pin).map _).sum_eq
    _ = _ := by
      let f := fun i : T2OrPartition.Id C => ((C.gates.get i).inputs.filter (· == (n+u.val))).map fun _ => i
      have allRows (xs : List (T2OrPartition.Id C)) :
          (((xs.filter (fun i => decide (L.op i=.or))).map (fun i => n+i.val)).map (weight C n (n+u.val))).sum =
            (xs.flatMap f).length := by
        induction xs with
        | nil => rfl
        | cons i xs ih =>
          have inp := layout_inputs (L.atIndex i)
          have eq : weight C n (n+u.val) (n+i.val)=(f i).length := by
            simp [weight,f,List.count_eq_length_filter]
          simp only [List.map_map,List.length_flatMap] at ih
          cases e : L.op i with
          | or => simp [e,eq,ih]
          | and =>
            have bad : n+u.val∉(C.gates.get i).inputs := fun hit => by
              have org := (physical_op L i).mp (only i (T2OrPartition.read_mem hit))
              simp [e] at org
            have no : f i=[] := by
              simp [f,List.filter_eq_nil_iff]
              intro a ha eq
              exact bad (eq ▸ ha)
            simp [e,no,ih]
      exact allRows _
end ThresholdExternalCount
