import IncidenceStartNormalization
namespace IncidenceHoistReaders
open CircuitRewire IncidenceStartNormalization

def operand (g : Gate) (left : Bool) := if left then g.left else g.right

private def atGate (u k : Nat) (g : Gate) : List (Nat × Bool) :=
  (if g.left = u then [(k,true)] else []) ++ (if g.right = u then [(k,false)] else [])

def occurrences {n} (C : Circuit n) (u : Nat) : List (Nat × Bool) :=
  (List.range C.size).flatMap fun k => atGate u k (C.code k)

def reader? {n} (C : Circuit n) (u : Nat) : Option (Nat × Bool) :=
  match occurrences C u with
  | [x] => some x
  | _ => none

private theorem at_length (u k : Nat) (g : Gate) :
    (atGate u k g).length = (if g.left = u then 1 else 0) + (if g.right = u then 1 else 0) := by
  by_cases hl : g.left = u <;> by_cases hr : g.right = u <;> simp [atGate,hl,hr]

theorem occurrence_count {n} (C : Circuit n) (u : Nat) :
    (occurrences C u).length = IncidenceStartNormalization.uses C u := by
  unfold occurrences IncidenceStartNormalization.uses
  induction List.range C.size with
  | nil => rfl
  | cons k ks ih => simp [at_length,ih]

private theorem at_mem (u j k : Nat) (g : Gate) (b : Bool) :
    (k,b) ∈ atGate u j g ↔ k = j ∧ operand g b = u := by
  by_cases hl : g.left = u <;> by_cases hr : g.right = u <;>
    cases b <;> simp [atGate,operand,hl,hr]

theorem occurrence_mem {n} (C : Circuit n) (u k : Nat) (b : Bool) :
    (k,b) ∈ occurrences C u ↔ k < C.size ∧ operand (C.code k) b = u := by
  unfold occurrences
  constructor
  · intro mem
    obtain ⟨j,hj,hg⟩ := List.mem_flatMap.mp mem
    obtain ⟨rfl,eq⟩ := (at_mem ..).mp hg
    exact ⟨List.mem_range.mp hj,eq⟩
  · rintro ⟨hk,eq⟩
    exact List.mem_flatMap.mpr ⟨k,List.mem_range.mpr hk,(at_mem ..).mpr ⟨rfl,eq⟩⟩

theorem unique_reader {n} (C : Circuit n) (u : Nat) (h : IncidenceStartNormalization.uses C u = 1) :
    ∃ g side, reader? C u = some (g,side) ∧ g < C.size ∧ operand (C.code g) side = u ∧
      ∀ k < C.size, ∀ b, operand (C.code k) b = u → k = g ∧ b = side := by
  obtain ⟨⟨g,side⟩,only⟩ := List.length_eq_one_iff.mp ((occurrence_count C u).trans h)
  have mem : (g,side) ∈ occurrences C u := by simp [only]
  obtain ⟨bound,read⟩ := (occurrence_mem ..).mp mem
  refine ⟨g,side,by simp [reader?,only],bound,read,?_⟩
  intro k hk b eq
  have mem := (occurrence_mem C u k b).mpr ⟨hk,eq⟩
  simpa [only,Prod.mk.injEq] using mem

#print axioms unique_reader
end IncidenceHoistReaders
