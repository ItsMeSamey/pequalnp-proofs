import ThresholdOrMultiplicity
open PEqualNP.CircuitLowerBounds ThresholdOrGroups
namespace ThresholdOrExtraction
def ports (C : Circuit) (n j : Nat) :=
  (((C.gates[j-n]?).map Gate.inputs).getD []).countP (fun w => decide (w<n))

theorem raw_top_branch (C : Circuit) (n p w : Nat) :
    rawTop (branch C n p w).val = if w<n then 1 else 0 := by
  rw [branch]
  split
  next raw => simp [rawTop,raw]
  next nr =>
    split <;> simp [rawTop,nr]

theorem raw_law {C : Circuit} {n p x y : Nat} (g : GateAt C n p .or x y) :
    rawTop (branch C n p x).val + rawTop (branch C n p y).val = ports C n p := by
  rw [raw_top_branch,raw_top_branch]
  simp [ports,gate_lookup g,ResidualSurplus.binary,List.countP_cons,Nat.add_comm]

theorem raw_branch {C : Circuit} {n : Nat} (p w : Nat) :
    RawBalanced (ports C n) (branch C n p w).val := by
  rw [branch]
  split
  · trivial
  · split
    next ex =>
      let h := ex.choose_spec.2.2
      let x := h.choose
      let y := h.choose_spec.choose
      have g : GateAt C n w .or x y := h.choose_spec.choose_spec
      exact ⟨raw_law g,raw_branch w x,raw_branch w y⟩
    next => trivial
termination_by w
decreasing_by all_goals first | exact g.leftEarlier | exact g.rightEarlier

theorem block_raw_count {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) (i : T2OrPartition.Id C) :
    (makeBlock layout pin i).rawSlots = ((makeBlock layout pin i).orIDs.map (ports C n)).sum := by
  unfold makeBlock
  split
  · rfl
  · rename_i e
    let g : GateAt C n (n+i.val) .or (layout.left i) (layout.right i) := e ▸ layout.atIndex i
    let t := (root C n (n+i.val) (layout.left i) (layout.right i) g).val
    have clean : RawBalanced (ports C n) t := ⟨raw_law g,raw_branch _ _,raw_branch _ _⟩
    change t.raws.length = (t.gates.map (ports C n)).sum
    simpa only [show rawTop t = 0 from rfl,Nat.zero_add] using raw_count_by_physical (ports C n) t clean

theorem forest_raw_count {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) :
    rawCount (forest layout pin) = ((allGates (forest layout pin)).map (ports C n)).sum := by
  unfold forest
  generalize fixed C n = xs
  induction xs with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons,rawCount,allGates,List.flatMap_cons,List.map_append,List.sum_cons,
      List.sum_append,block_raw_count] at *
    exact congrArg (_ + ·) ih

def orIndex {C : Circuit} {n : Nat} (layout : Layout C n) :=
  ((List.finRange C.gates.length).filter (fun i => decide (layout.op i=.or))).map
    (fun i => n+i.val)

theorem ids_permute {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) :
    (allGates (forest layout pin)).Perm (orIndex layout) := by
  have inj : Function.Injective (fun i : T2OrPartition.Id C => n+i.val) := by
    intro a b eq; change n+a.val=n+b.val at eq; exact Fin.ext (Nat.add_left_cancel eq)
  apply (List.perm_ext_iff_of_nodup (forest_nodup layout pin)
    (((List.nodup_finRange _).filter _).map inj)).mpr
  intro j
  constructor
  · intro hw
    obtain ⟨i,rfl⟩ := forest_range layout pin _ hw
    have pos := List.count_pos_iff.mpr hw
    rw [physical_count layout pin i] at pos
    have hi : layout.op i=.or := by split at pos <;> simp_all
    exact List.mem_map.mpr ⟨i,by simp [hi],rfl⟩
  · intro hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have op : layout.op i=.or := by simpa using hi
    apply List.count_pos_iff.mp
    simp [physical_count layout pin i,op]

theorem physical_raw_total {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) :
    rawCount (forest layout pin) = ((orIndex layout).map (ports C n)).sum :=
  (forest_raw_count layout pin).trans (((ids_permute layout pin).map (ports C n)).sum_eq)

end ThresholdOrExtraction
