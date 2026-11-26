import GateSurplus

namespace T2PhysicalOverride
open PEqualNP.CircuitLowerBounds
open ResidualSurplus

def shift (g : Gate) : Gate := ⟨g.op, g.inputs.map Nat.succ⟩

theorem val_shift (g : Gate) (b : Bool) (w : List Bool) :
    val (shift g) (b :: w) = val g w := by
  simp [val, shift, List.map_map, Function.comp_def, List.getD_eq_getElem?_getD]

theorem run_shift (gs : List Gate) (b : Bool) (w : List Bool) :
    run (gs.map shift) (b :: w) = b :: run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change run (gs.map shift) ((b::w) ++ [val (shift g) (b::w)]) =
      b :: run gs (w ++ [val g w])
    rw [val_shift]
    exact ih (w ++ [val g w])

/-- Use the same gate kind for the forced row. Either binary idempotent
operation on two copies of wire zero simply reads the new raw value. -/
theorem forced_row (o : Op) (b : Bool) (w : List Bool) :
    val (binary o 0 0) (b :: w) = b := by
  cases o <;> cases b <;> rfl

def edited (pre post : List Gate) (o : Op) : List Gate :=
  pre.map shift ++ binary o 0 0 :: post.map shift

theorem size_edit (pre post : List Gate) (o : Op) (g : Gate) :
    (edited pre post o).length = (pre ++ g :: post).length := by simp [edited]

theorem ops_edit (pre post : List Gate) (o : Op) (x y : Nat) :
    (edited pre post o).map Gate.op = (pre ++ binary o x y :: post).map Gate.op := by
  simp [edited, shift, binary, List.map_map, Function.comp_def]

theorem run_edited (pre post : List Gate) (o : Op) (b : Bool) (w : List Bool) :
    run (edited pre post o) (b :: w) =
      b :: run post (run pre w ++ [b]) := by
  have split (a d : List Gate) (v : List Bool) :
      run (a ++ d) v = run d (run a v) := by simp [run, List.foldl_append]
  rw [edited, split, run_shift]
  change run (post.map shift) ((b :: run pre w) ++ [val (binary o 0 0) (b :: run pre w)]) = _
  rw [forced_row]
  exact run_shift post b (run pre w ++ [b])

theorem eval_edited (pre post : List Gate) (o : Op) (b : Bool) (w : List Bool)
    (out : Nat) :
    Circuit.eval ⟨edited pre post o,out+1⟩ (b :: w) =
      (run post (run pre w ++ [b])).getD out false := by
  change (run (edited pre post o) (b :: w)).getD (out+1) false = _
  rw [run_edited]
  simp [List.getD_eq_getElem?_getD]

def rawShift : Raw → Raw
  | (o,x,y) => (o,x+1,y+1)

def native (r : Raw) : Gate := binary r.1 r.2.1 r.2.2

def rawEdited (pre post : List Raw) (o : Op) : List Raw :=
  pre.map rawShift ++ (o,0,0) :: post.map rawShift

theorem native_shift (r : Raw) : native (rawShift r) = shift (native r) := by
  obtain ⟨o,x,y⟩ := r
  rfl

theorem edit_raw_correct (pre post : List Raw) (o : Op) :
    (rawEdited pre post o).map native = edited (pre.map native) (post.map native) o := by
  simp only [rawEdited, edited, List.map_append, List.map_cons, List.map_map, Function.comp_def, native_shift]
  rfl

#print axioms eval_edited
end T2PhysicalOverride
