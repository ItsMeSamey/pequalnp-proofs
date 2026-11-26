import PEqualNP.Defs.MetaComplexityLgpMono

namespace T2OrPartition
open PEqualNP.CircuitLowerBounds
abbrev Id (C : Circuit) := Fin C.gates.length

/-- One entry per operand occurrence, including duplicate reads by a single gate. -/
def readers (C : Circuit) (wire : Nat) : List (Id C) :=
  (List.finRange C.gates.length).flatMap fun j =>
    ((C.gates.get j).inputs.filter fun u => u == wire).map fun _ => j

def isOr (C : Circuit) (i : Id C) : Bool := match (C.gates.get i).op with | .or => true | _ => false

def next (C : Circuit) (n : Nat) (i : Id C) : Option {j : Id C // i < j} :=
  match readers C (n + i.val) with
  | [j] => if isOr C i ∧ isOr C j ∧ C.output ≠ n+i.val then
             if h : i < j then some ⟨j,h⟩ else none
           else none
  | _ => none

def owner (C : Circuit) (n : Nat) (i : Id C) : Id C :=
  match next C n i with
  | none => i
  | some j => owner C n j.val
termination_by C.gates.length - i.val
decreasing_by have h := j.property; have hh := j.val.isLt; change i.val < j.val.val at h; omega

theorem owner_of_next (C : Circuit) (n : Nat) (i : Id C) (j : {j : Id C // i < j})
    (h : next C n i = some j) : owner C n i = owner C n j.val := by
  rw [owner, h]

theorem owner_of_stop (C : Circuit) (n : Nat) (i : Id C) (h : next C n i = none) :
    owner C n i = i := by rw [owner, h]

theorem owner_spec (C : Circuit) (n : Nat) (i : Id C) :
    i ≤ owner C n i ∧ next C n (owner C n i) = none := by
  cases h : next C n i with
  | none => rw [owner_of_stop C n i h]; exact ⟨le_rfl,h⟩
  | some j =>
    rw [owner_of_next C n i j h]
    have ih := owner_spec C n j.val
    exact ⟨le_trans (le_of_lt j.property) ih.1, ih.2⟩
termination_by C.gates.length - i.val
decreasing_by have h' := j.val.isLt; have hh := j.property; change i.val < j.val.val at hh; omega

theorem owner_idempotent (C : Circuit) (n : Nat) (i : Id C) :
    owner C n (owner C n i) = owner C n i :=
  owner_of_stop C n _ (owner_spec C n i).2

def block (C : Circuit) (n : Nat) (r : Id C) : List (Id C) :=
  (List.finRange C.gates.length).filter fun i => owner C n i == r

theorem mem_block (C : Circuit) (n : Nat) (r i : Id C) :
    i ∈ block C n r ↔ owner C n i = r := by simp [block]
theorem blocks_disjoint (C : Circuit) (n : Nat) {r s i : Id C}
    (hi : i ∈ block C n r) (hj : i ∈ block C n s) : r = s :=
  ((mem_block C n r i).mp hi).symm.trans ((mem_block C n s i).mp hj)

theorem covers (C : Circuit) (n : Nat) (i : Id C) :
    ∃ r, next C n r = none ∧ i ∈ block C n r :=
  ⟨owner C n i,(owner_spec C n i).2,(mem_block C n _ i).mpr rfl⟩

theorem read_mem {C : Circuit} {j : Id C} {w : Nat} (read : w ∈ (C.gates.get j).inputs) :
    j ∈ readers C w := by
  apply List.mem_flatMap.mpr
  refine ⟨j, by simp, ?_⟩
  apply List.mem_map.mpr
  exact ⟨w,List.mem_filter.mpr ⟨read,by simp⟩,rfl⟩

theorem next_readers {C : Circuit} {n : Nat} {i : Id C} {j : {j : Id C // i<j}}
    (edge : next C n i = some j) : readers C (n+i.val) = [j.val] := by
  unfold next at edge
  split at edge
  next k hh =>
    split at edge
    · split at edge
      · cases edge
        exact hh
      · contradiction
    · contradiction
  next => contradiction

theorem boundary_root {C : Circuit} {n : Nat} {i j : Id C}
    (read : n+i.val ∈ (C.gates.get j).inputs)
    (cut : ∀ h : i<j, next C n i ≠ some ⟨j,h⟩) :
    next C n i = none := by
  cases edge : next C n i with
  | none => rfl
  | some q =>
    have mem := read_mem read
    rw [next_readers edge] at mem
    have eq : j=q.val := List.mem_singleton.mp mem
    subst j
    exact False.elim (cut q.property edge)
#print axioms covers
#print axioms boundary_root
end T2OrPartition
