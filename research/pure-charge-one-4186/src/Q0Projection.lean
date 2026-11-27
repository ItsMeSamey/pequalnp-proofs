import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4186_aux.Q0.Projection

open PEqualNP.CircuitLowerBounds

/-- None denotes symbolic true. Some i denotes an already available projected wire. -/
abbrev Ref := Option ℕ

def value (w : List Bool) : Ref → Bool
  | none => true
  | some i => w.getD i false

def valid (next : ℕ) : Ref → Prop
  | none => True
  | some i => i < next

/-- Emit an AND only when both projected pins name physical wires. -/
def emit : Ref → Ref → List Gate
  | some i, some j => [⟨.and, [i,j]⟩]
  | _, _ => []

def dest (next : ℕ) : Ref → Ref → Ref
  | none, q => q
  | some i, none => some i
  | some _, some _ => some next

def run (w : List Bool) (p q : Ref) : List Bool :=
  (emit p q).foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w

theorem emit_count (p q : Ref) : (emit p q).length ≤ 1 := by
  cases p <;> cases q <;> simp [emit]

theorem emit_binary {k : ℕ} {p q : Ref} (hp : valid k p) (hq : valid k q) :
    ∀ g ∈ emit p q, g.op = .and ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < k := by
  cases p <;> cases q <;> simp_all [emit, valid]

theorem dest_valid {k : ℕ} {p q : Ref} (hp : valid k p) (hq : valid k q) :
    valid (k + (emit p q).length) (dest k p q) := by
  cases p <;> cases q <;> simp_all [emit, valid, dest]

theorem run_length (w : List Bool) (p q : Ref) :
    (run w p q).length = w.length + (emit p q).length := by
  cases p <;> cases q <;> simp [run, emit]

theorem run_keeps {w : List Bool} {i : ℕ} (hi : i < w.length) (p q : Ref) :
    (run w p q).getD i false = w.getD i false := by
  cases p <;> cases q <;> simp [run, emit, List.getD, List.getElem?_append_left hi]

theorem run_value (w : List Bool) (p q : Ref) :
    value (run w p q) (dest w.length p q) = (value w p && value w q) := by
  cases p <;> cases q <;> simp [value, run, emit, dest, GateOp.eval, List.getD]

/-- Affected pins represent g AND their projected value. Unaffected pins keep their value. -/
def original (g affected v : Bool) := if affected then g && v else v

theorem factor_step (w : List Bool) (g left right : Bool) (p q : Ref)
    (affected : left = true ∨ right = true) :
    (original g left (value w p) && original g right (value w q)) =
    (g && value (run w p q) (dest w.length p q)) := by
  rw [run_value]
  cases g <;> cases left <;> cases right <;> simp_all [original]

/-- The distinguished original wire g itself has the factored representation g AND true. -/
theorem source_value (w : List Bool) (g : Bool) : original g true (value w none) = g := by
  simp [original, value]

theorem direct_reader (p q : Ref) (h : p = none ∨ q = none) :
    emit p q = [] := by
  rcases h with rfl | rfl
  · rfl
  · cases p <;> rfl

theorem repeated_source (k : ℕ) : emit none none = [] ∧ dest k none none = none :=
  ⟨rfl, rfl⟩

/-- A below-F top cannot project to symbolic true if g is dirty. -/
theorem top_has_wire {X : Type*} {F g H : X → Bool} {w : X → List Bool} {p : Ref}
    (dirty : ∃ x, g x = true ∧ F x = false)
    (clean : ∀ x, H x = true → F x = true)
    (factor : ∀ x, H x = (g x && value (w x) p)) : ∃ i, p = some i := by
  cases p with
  | none =>
    obtain ⟨x, hg, hF⟩ := dirty
    have hH : H x = true := by simpa [hg, value] using factor x
    have := clean x hH
    simp_all
  | some i => exact ⟨i, rfl⟩

end PEqualNP.Outside.L_meta_4186_aux.Q0.Projection
