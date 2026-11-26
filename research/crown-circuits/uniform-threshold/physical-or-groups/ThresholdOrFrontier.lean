import ThresholdOrExtraction
open PEqualNP.CircuitLowerBounds ThresholdOrGroups
namespace ThresholdOrExtraction

theorem forest_ordered {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) :
    (forest layout pin).Pairwise (fun a b => a.out < b.out) := by
  unfold forest
  rw [List.pairwise_map]
  have h : (fixed C n).Pairwise (· < ·) :=
    (List.pairwise_lt_finRange C.gates.length).filter _
  apply h.imp
  intro a b lt
  simp only [makeBlock_out]
  exact Nat.add_lt_add_left lt _

theorem mem_roots {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat) (i : T2OrPartition.Id C)
    (stop : T2OrPartition.next C n i = none) :
    makeBlock layout pin i ∈ forest layout pin := by
  apply List.mem_map.mpr
  exact ⟨i,by simp [fixed,stop],rfl⟩

theorem forest_book {C : Circuit} {n : Nat} (layout : Layout C n)
    (pin : T2OrPartition.Id C → Nat)
    (external : ∀ i ∈ fixed C n, ∀ w ∈ (makeBlock layout pin i).exts,
      ∃ d : T2OrPartition.Id C, T2OrPartition.next C n d = none ∧ w=n+d.val ∧ d < i) :
    Book C n [] (forest layout pin) := by
  apply book_of_earlier _ _ (forest_checked layout pin) (forest_ordered layout pin)
  intro b hb w hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  obtain ⟨d,hd,rfl,lt⟩ := external i hi w hw
  exact Or.inr ⟨_,mem_roots layout pin d hd,makeBlock_out layout pin d,
    by rw [makeBlock_out]; exact Nat.add_lt_add_left lt _⟩

theorem next_is_or {C : Circuit} {n : Nat} {i : T2OrPartition.Id C}
    {j : {j : T2OrPartition.Id C // i<j}} (h : T2OrPartition.next C n i = some j) :
    T2OrPartition.isOr C i = true ∧ T2OrPartition.isOr C j.val = true := by
  unfold T2OrPartition.next at h
  split at h
  next k _ =>
    split at h
    next ok =>
      split at h
      · cases h; exact ⟨ok.1,ok.2.1⟩
      · contradiction
    next => contradiction
  next => contradiction

theorem physical_op {C : Circuit} {n : Nat} (layout : Layout C n)
    (i : T2OrPartition.Id C) :
    T2OrPartition.isOr C i = true ↔ layout.op i = .or := by
  have lk := gate_lookup (layout.atIndex i)
  have gl : C.gates.get i =
      ResidualSurplus.binary (layout.op i) (layout.left i) (layout.right i) := by
    simpa using lk
  unfold T2OrPartition.isOr
  rw [gl]
  cases h : layout.op i <;> simp [ResidualSurplus.binary,ResidualSurplus.gateOp]

theorem next_layout {C : Circuit} {n : Nat} (layout : Layout C n)
    {i : T2OrPartition.Id C} {j : {j : T2OrPartition.Id C // i<j}}
    (edge : T2OrPartition.next C n i = some j) :
    GateAt C n (n+i.val) .or (layout.left i) (layout.right i) :=
  (physical_op layout i |>.mp (next_is_or edge).1) ▸ layout.atIndex i

def ExternalRoot (C : Circuit) (n w : Nat) : Prop :=
  ∃ d : T2OrPartition.Id C, T2OrPartition.next C n d = none ∧ w = n+d.val

theorem external_stop {C : Circuit} {n : Nat} (layout : Layout C n)
    (i d : T2OrPartition.Id C) (read : n+d.val ∈ (C.gates.get i).inputs)
    (closed : ¬(∃ k : T2OrPartition.Id C, n+d.val = n+k.val ∧
      (∃ j : {j : T2OrPartition.Id C // k<j},
        T2OrPartition.next C n k = some j ∧ n+i.val = n+j.val.val) ∧
      ∃ x y, GateAt C n (n+d.val) .or x y)) :
    ExternalRoot C n (n+d.val) := by
  refine ⟨d,T2OrPartition.boundary_root read ?_,rfl⟩
  intro lt edge
  apply closed
  exact ⟨d,rfl,⟨⟨i,lt⟩,edge,rfl⟩,_,_,next_layout layout edge⟩

end ThresholdOrExtraction
