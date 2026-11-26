import ThresholdRegularSource
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ThresholdRegularSource
namespace ThresholdNamedIncidence

def weight (C : Circuit) (n w j : Nat) :=
  (((C.gates[j-n]?).map Gate.inputs).getD []).count w

private theorem portWeight {C : Circuit} {n w p l r : Nat} (g : GateAt C n p .or l r) :
    weight C n w p = (if l=w then 1 else 0) + (if r=w then 1 else 0) := by
  simp [weight,gate_lookup g,ResidualSurplus.binary,List.count_cons,Nat.add_comm]

theorem branch_count (C : Circuit) (n w : Nat) (raw : w<n) (p z : Nat) :
    let t := (branch C n p z).val
    t.raws.count w = (if z=w then 1 else 0) + (t.gates.map (weight C n w)).sum := by
  rw [branch]
  split
  next small => simp [Tree.raws,Tree.gates,List.count_cons]
  next large =>
    have ne : z≠w := by omega
    split
    next ex =>
      let h := ex.choose_spec.2.2
      let l := h.choose
      let r := h.choose_spec.choose
      have g : GateAt C n z .or l r := h.choose_spec.choose_spec
      have left := branch_count C n w raw z l
      have right := branch_count C n w raw z r
      simp only [Tree.raws,Tree.gates,List.count_append,List.map_cons,List.sum_cons,List.map_append,List.sum_append,ne,ite_false,zero_add]
      dsimp only at left right
      rw [left,right,portWeight g]
      dsimp only [l,r,h] at *
      omega
    next => simp [Tree.raws,Tree.gates,ne]
termination_by z
decreasing_by all_goals first | exact g.leftEarlier | exact g.rightEarlier

theorem block_count {C : Circuit} {n w : Nat} (L : Layout C n) (hw : w<n)
    (pin : T2OrPartition.Id C → Nat) (i : T2OrPartition.Id C) :
    (rawList (makeBlock L pin i)).count w =
      ((makeBlock L pin i).orIDs.map (weight C n w)).sum := by
  unfold makeBlock
  split
  · rfl
  · rename_i e
    let g : GateAt C n (n+i.val) .or (L.left i) (L.right i) := e ▸ L.atIndex i
    simp only [rawList,Block.orIDs,root,Tree.raws,Tree.gates,List.count_append,List.map_cons,
      List.map_append,List.sum_cons,List.sum_append]
    rw [branch_count C n w hw,branch_count C n w hw,portWeight g]
    omega

theorem point_count {C : Circuit} {n w : Nat} (L : Layout C n) (reg : MeetsInternal L)
    (hw : w<n) (pin : T2OrPartition.Id C → Nat) :
    ((forest L pin).map (fun b => (rawList b).count w)).sum = (T2OrPartition.readers C w).length := by
  have inv (xs : List (T2OrPartition.Id C)) :
      ((xs.map (makeBlock L pin)).map (fun b => (rawList b).count w)).sum =
        ((allGates (xs.map (makeBlock L pin))).map (weight C n w)).sum := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      simp only [List.map_cons,List.sum_cons,allGates,List.flatMap_cons,List.map_append,List.sum_append,block_count L hw] at *
      exact congrArg (_+·) ih
  calc
    _ = _ := inv (fixed C n)
    _ = ((orIndex L).map (weight C n w)).sum := ((ids_permute L pin).map _).sum_eq
    _ = _ := by
      let f := fun i : T2OrPartition.Id C => ((C.gates.get i).inputs.filter (· == w)).map fun _ => i
      have allRows (xs : List (T2OrPartition.Id C)) :
          (((xs.filter (fun i => decide (L.op i=.or))).map (fun i => n+i.val)).map (weight C n w)).sum =
            (xs.flatMap f).length := by
        induction xs with
        | nil => rfl
        | cons i xs ih =>
          have inp := layout_inputs (L.atIndex i)
          have eq : weight C n w (n+i.val)=(f i).length := by
            simp [weight,f,List.count_eq_length_filter]
          simp only [List.map_map,List.length_flatMap] at ih
          cases e : L.op i with
          | or => simp [e,eq,ih]
          | and =>
            have h := reg i e
            have nl : L.left i≠w := by omega
            have nr : L.right i≠w := by omega
            have no : f i=[] := by
              unfold f
              rw [inp]; simp [nl,nr]
            simp [e,no,ih]
      exact allRows _
end ThresholdNamedIncidence
