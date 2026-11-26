import ThresholdOrFrontier
open PEqualNP.CircuitLowerBounds ThresholdOrGroups
namespace ThresholdOrExtraction
theorem layout_inputs {C : Circuit} {n : Nat} {i : T2OrPartition.Id C}
    {o : ResidualSurplus.Op} {x y : Nat} (gate : GateAt C n (n+i.val) o x y) :
    (C.gates.get i).inputs = [x,y] := by
  have lk := gate_lookup gate
  have gl : C.gates.get i = ResidualSurplus.binary o x y := by simpa using lk
  rw [gl]; rfl

theorem branch_frontier {C : Circuit} {n : Nat} (layout : Layout C n)
    (w : Nat) (i : T2OrPartition.Id C) (bound : w<n+i.val)
    (read : w ∈ (C.gates.get i).inputs) :
    ∀ u∈(branch C n (n+i.val) w).val.exts, ExternalRoot C n u ∧ u<n+i.val := by
  rw [branch]
  split
  · simp [Tree.exts]
  · split
    next ex =>
      let d := ex.choose
      have eq : w=n+d.val := ex.choose_spec.1
      let witnesses := ex.choose_spec.2.2
      let x := witnesses.choose
      let y := witnesses.choose_spec.choose
      have gate : GateAt C n w .or x y := witnesses.choose_spec.choose_spec
      have gate' : GateAt C n (n+d.val) .or x y := eq ▸ gate
      have ins := layout_inputs gate'
      intro u hu
      change u ∈ (branch C n w x).val.exts ++ (branch C n w y).val.exts at hu
      rcases List.mem_append.mp hu with hl|hr
      · rw [eq] at hl
        have hh := branch_frontier layout x d gate'.leftEarlier (by rw [ins]; simp) u hl
        exact ⟨hh.1,by omega⟩
      · rw [eq] at hr
        have hh := branch_frontier layout y d gate'.rightEarlier (by rw [ins]; simp) u hr
        exact ⟨hh.1,by omega⟩
    next closed =>
      intro u hu
      have heq : u=w := by simpa [Tree.exts] using hu
      subst u
      have raw : n ≤ w := by omega
      let d : T2OrPartition.Id C := ⟨w-n, by have hi := i.isLt; omega⟩
      have eq : w=n+d.val := by dsimp [d]; omega
      have rr := external_stop layout i d (eq ▸ read) (eq ▸ closed)
      exact ⟨eq.symm ▸ rr,bound⟩
termination_by w
decreasing_by all_goals first | exact gate.leftEarlier | exact gate.rightEarlier

/-- Exactly the regular-case condition needed at an AND root. -/
def MeetsInternal {C : Circuit} {n : Nat} (layout : Layout C n) : Prop :=
  ∀ i, layout.op i = .and → n ≤ layout.left i ∧ n ≤ layout.right i

theorem root_externals {C : Circuit} {n : Nat} (layout : Layout C n)
    (regular : MeetsInternal layout) (pin : T2OrPartition.Id C → Nat) (i : T2OrPartition.Id C)
    (w : Nat) (hw : w ∈ (makeBlock layout pin i).exts) :
    ExternalRoot C n w ∧ w<n+i.val := by
  unfold makeBlock at hw
  split at hw
  next eq =>
    have gate := layout.atIndex i
    have ins := layout_inputs gate
    have ext : w=layout.left i ∨ w=layout.right i := by simpa [Block.exts] using hw
    have raw : n ≤ w := by rcases ext with rfl|rfl <;> exact (by first | exact (regular i eq).1 | exact (regular i eq).2)
    have lt : w<n+i.val := by rcases ext with rfl|rfl <;> first | exact gate.leftEarlier | exact gate.rightEarlier
    let d : T2OrPartition.Id C := ⟨w-n,by have hi := i.isLt; omega⟩
    have wd : w=n+d.val := by dsimp [d]; omega
    have rd : w ∈ (C.gates.get i).inputs := by rw [ins]; simpa using ext
    have stop : T2OrPartition.next C n d=none := by
      apply T2OrPartition.boundary_root (wd ▸ rd)
      intro earlier edge
      have e := (physical_op layout i).mp (next_is_or edge).2
      simp [eq] at e
    exact ⟨⟨d,stop,wd⟩,lt⟩
  next eq =>
    have gate := layout.atIndex i
    have ins := layout_inputs gate
    change w ∈ (branch C n (n+i.val) (layout.left i)).val.exts ++
        (branch C n (n+i.val) (layout.right i)).val.exts at hw
    rcases List.mem_append.mp hw with left|right
    · exact branch_frontier layout _ i gate.leftEarlier (by rw [ins]; simp) w left
    · exact branch_frontier layout _ i gate.rightEarlier (by rw [ins]; simp) w right

theorem extracted_book {C : Circuit} {n : Nat} (layout : Layout C n)
    (regular : MeetsInternal layout) (pin : T2OrPartition.Id C → Nat) :
    Book C n [] (forest layout pin) := by
  apply forest_book
  intro i _ w hw
  obtain ⟨⟨d,stop,eq⟩,lt⟩ := root_externals layout regular pin i w hw
  exact ⟨d,stop,eq,by change d.val < i.val; omega⟩

#print axioms extracted_book
end ThresholdOrExtraction
