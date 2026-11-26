import ThresholdOrFrontier
open PEqualNP.CircuitLowerBounds ThresholdOrGroups
namespace ThresholdOrExtraction

private theorem length_one_image {α β : Type} (f : α → List β) {xs : List α}
    {x : α} (hx : x∈xs) : (f x).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl|rest
    · simp
    · have := ih rest; simp only [List.flatMap_cons,List.length_append]; omega

theorem singleton_port {C : Circuit} {w : Nat} {j : T2OrPartition.Id C}
    (singleton : T2OrPartition.readers C w = [j]) :
    ((C.gates.get j).inputs.filter (· == w)).length=1 := by
  let f := fun k : T2OrPartition.Id C =>
    ((C.gates.get k).inputs.filter (· == w)).map (fun _ => k)
  have whole : (List.finRange C.gates.length).flatMap f = [j] := singleton
  have small := length_one_image f (List.mem_finRange j)
  rw [whole] at small
  have existsRead : j ∈ (List.finRange C.gates.length).flatMap f := by simp [whole]
  obtain ⟨k,_,mem⟩ := List.mem_flatMap.mp existsRead
  obtain ⟨u,hu,eq⟩ := List.mem_map.mp mem
  subst k
  have pos := List.length_pos_of_mem hu
  simp only [f,List.length_map,List.length_singleton] at small
  omega

theorem top_of_ne {C : Circuit} {n parent w q : Nat} (ne : w≠q) :
    atRoot q (branch C n parent w).val=0 := by
  rw [branch]
  split
  · rfl
  · split
    · simp [atRoot,ne]
    · rfl

theorem top_private {C : Circuit} {n : Nat} (layout : Layout C n)
    {i : T2OrPartition.Id C} {j : {j : T2OrPartition.Id C // i<j}}
    (edge : T2OrPartition.next C n i = some j) (p : Nat) :
    atRoot (n+i.val) (branch C n p (n+i.val)).val = if p=n+j.val.val then 1 else 0 := by
  rw [branch]
  split
  next h => omega
  next =>
    split
    next ex =>
      obtain ⟨d,eq,⟨r,er,pr⟩,_⟩ := ex
      have di : d=i := Fin.ext (by omega)
      subst d
      rw [edge] at er
      cases er
      simp [atRoot,pr]
    next ne =>
      by_cases yes : p=n+j.val.val
      · exact False.elim (ne ⟨i,rfl,⟨j,edge,yes⟩,_,_,next_layout layout edge⟩)
      · simp [atRoot,yes]

theorem top_stopped {C : Circuit} {n : Nat} {i : T2OrPartition.Id C}
    (stop : T2OrPartition.next C n i=none) (p w : Nat) :
    atRoot (n+i.val) (branch C n p w).val=0 := by
  by_cases eq : w=n+i.val
  · subst w
    rw [branch]
    split
    next h => omega
    next =>
      split
      next ex =>
        obtain ⟨d,eq,⟨r,er,_⟩,_⟩ := ex
        have di : d=i := Fin.ext (by omega)
        subst d
        rw [stop] at er; contradiction
      next => rfl
  · exact top_of_ne eq

theorem private_slot_weight {C : Circuit} {n : Nat} (layout : Layout C n)
    {i : T2OrPartition.Id C} {j : {j : T2OrPartition.Id C // i<j}}
    (edge : T2OrPartition.next C n i = some j) (p x y : Nat) (gate : GateAt C n p .or x y) :
    atRoot (n+i.val) (branch C n p x).val + atRoot (n+i.val) (branch C n p y).val =
      if p=n+j.val.val then 1 else 0 := by
  have leftWeight (w : Nat) :
      atRoot (n+i.val) (branch C n p w).val =
        if w=n+i.val then (if p=n+j.val.val then 1 else 0) else 0 := by
    by_cases eq : w=n+i.val
    · subst w; simp only [if_true]; exact top_private layout edge p
    · simp [eq,top_of_ne eq]
  rw [leftWeight,leftWeight]
  by_cases pp : p=n+j.val.val
  · subst p
    have gl : C.gates.get j.val = ResidualSurplus.binary .or x y := by
      simpa using gate_lookup gate
    have single := singleton_port (T2OrPartition.next_readers edge)
    change ((C.gates.get j.val).inputs.filter (· == n+i.val)).length = 1 at single
    rw [gl] at single
    by_cases lx : x=n+i.val <;> by_cases ry : y=n+i.val <;>
      simp_all [ResidualSurplus.binary]
  · simp [pp]

theorem branch_balanced {C : Circuit} {n : Nat} (layout : Layout C n) (q : Nat)
    (weight : Nat → Nat)
    (law : ∀ p x y, GateAt C n p .or x y →
      atRoot q (branch C n p x).val + atRoot q (branch C n p y).val = weight p)
    (p w : Nat) : Balanced q weight (branch C n p w).val := by
  rw [branch]
  split
  · trivial
  · split
    next ex =>
      let h := ex.choose_spec.2.2
      let x := h.choose
      let y := h.choose_spec.choose
      have gate : GateAt C n w .or x y := h.choose_spec.choose_spec
      exact ⟨law _ _ _ gate, branch_balanced layout q weight law w x,
        branch_balanced layout q weight law w y⟩
    next => trivial
termination_by w
decreasing_by all_goals first | exact gate.leftEarlier | exact gate.rightEarlier

theorem root_balanced {C : Circuit} {n : Nat} (layout : Layout C n) (q : Nat)
    (weight : Nat → Nat)
    (law : ∀ p x y, GateAt C n p .or x y →
      atRoot q (branch C n p x).val + atRoot q (branch C n p y).val = weight p)
    (p x y : Nat) (g : GateAt C n p .or x y) :
    Balanced q weight (root C n p x y g).val :=
  ⟨law _ _ _ g,branch_balanced layout q weight law p x,branch_balanced layout q weight law p y⟩

end ThresholdOrExtraction
