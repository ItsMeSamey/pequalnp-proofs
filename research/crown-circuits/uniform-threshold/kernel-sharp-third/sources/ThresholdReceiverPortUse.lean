import ThresholdSecondaryReceivers
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdOrGroups
namespace ThresholdSecondaryReceivers
variable {C : Circuit} {n : Nat} (L : Layout C n)
private theorem branch_owner (w : Nat) (i : Id C) (read : w∈(C.gates.get i).inputs) (u : Id C)
    (use : n+u.val∈(branch C n (n+i.val) w).val.exts) : owner C n i∈signature C n u := by
  rw [branch] at use
  split at use
  · simp [Tree.exts] at use
  · split at use
    next ex =>
      let d := ex.choose
      have eq : w=n+d.val := ex.choose_spec.1
      obtain ⟨j,edge,idx⟩ := ex.choose_spec.2.1
      have ji : j.val=i := Fin.ext (Nat.add_left_cancel idx.symm)
      have ow : owner C n d=owner C n i := (owner_of_next C n d j edge).trans (congrArg (owner C n) ji)
      let witnesses := ex.choose_spec.2.2
      let x := witnesses.choose
      let y := witnesses.choose_spec.choose
      have gate : GateAt C n w .or x y := witnesses.choose_spec.choose_spec
      have gate' : GateAt C n (n+d.val) .or x y := eq ▸ gate
      have ins := layout_inputs gate'
      change n+u.val∈(branch C n w x).val.exts ++ (branch C n w y).val.exts at use
      rw [←ow]
      rcases List.mem_append.mp use with l|r
      · rw [eq] at l
        exact branch_owner x d (by rw [ins]; simp) u l
      · rw [eq] at r
        exact branch_owner y d (by rw [ins]; simp) u r
    next closed =>
      have e : n+u.val=w := by simpa [Tree.exts] using use
      apply List.mem_toFinset.mpr
      exact List.mem_map.mpr ⟨i,read_mem (e.symm ▸ read),rfl⟩
termination_by w
decreasing_by all_goals first | exact gate.leftEarlier | exact gate.rightEarlier

theorem receiver_use (pin : Id C → Nat) (u : Id C) (b : Block) (mem : b∈forest L pin)
    (use : n+u.val∈b.exts) : ∃ i∈signature C n u, b.out=n+i.val := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
  have stop : next C n i=none := by simpa [fixed] using hi
  refine ⟨i,?_,makeBlock_out L pin i⟩
  rw [←owner_of_stop C n i stop]
  unfold makeBlock at use
  have ins := layout_inputs (L.atIndex i)
  split at use
  · apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨i,read_mem (by rw [ins]; exact use),rfl⟩
  · change n+u.val∈(branch C n (n+i.val) (L.left i)).val.exts ++
        (branch C n (n+i.val) (L.right i)).val.exts at use
    rcases List.mem_append.mp use with l|r
    · exact branch_owner _ i (by rw [ins]; simp) u l
    · exact branch_owner _ i (by rw [ins]; simp) u r
end ThresholdSecondaryReceivers
