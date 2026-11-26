import T2PhysicalOverride
import T2SoleReader

namespace T2PhysicalMaximum
open PEqualNP.CircuitLowerBounds
open ResidualSurplus
open T2PhysicalOverride

def Imp (a b : Bool) : Prop := a = true → b = true

inductive BankLE : List Bool → List Bool → Prop
  | nil : BankLE [] []
  | cons {u v : List Bool} {a b : Bool} : Imp a b → BankLE u v → BankLE (a::u) (b::v)

theorem BankLE.get {u v : List Bool} (h : BankLE u v) (i : Nat) :
    Imp (u.getD i false) (v.getD i false) := by
  induction h generalizing i with
  | nil => exact fun hb => hb
  | cons ab _ ih =>
    cases i with
    | zero => exact ab
    | succ i => exact ih i

theorem BankLE.push {u v : List Bool} (h : BankLE u v) {a b : Bool} (ab : Imp a b) :
    BankLE (u ++ [a]) (v ++ [b]) := by
  induction h with
  | nil => exact .cons ab .nil
  | cons xy _ ih => exact .cons xy ih

theorem act_mono (o : Op) {a b c d : Bool} (ab : Imp a b) (cd : Imp c d) :
    Imp (act o a c) (act o b d) := by
  cases o <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all [Imp,act]

theorem val_mono (r : Raw) {u v : List Bool} (h : BankLE u v) :
    Imp (val (native r) u) (val (native r) v) := by
  obtain ⟨o,x,y⟩ := r
  let t : Row := ⟨o,x,y,.both⟩
  change Imp (val t.full u) (val t.full v)
  rw [row_full, row_full]
  exact act_mono _ (h.get _) (h.get _)

theorem run_mono (rs : List Raw) {u v : List Bool} (h : BankLE u v) :
    BankLE (run (rs.map native) u) (run (rs.map native) v) := by
  induction rs generalizing u v with
  | nil => exact h
  | cons r t ih =>
    apply ih
    exact h.push (val_mono r h)

def response (pre post : List Raw) (out : Nat) (inputs : List Bool) (override : Bool) :=
  (run (post.map native) (run (pre.map native) inputs ++ [override])).getD out false

def computed (pre : List Raw) (r : Raw) (inputs : List Bool) :=
  val (native r) (run (pre.map native) inputs)

theorem eval_original (pre post : List Raw) (r : Raw) (out : Nat) (w : List Bool) :
    Circuit.eval ⟨(pre ++ r::post).map native,out⟩ w =
      response pre post out w (computed pre r w) := by
  change (run ((pre ++ r::post).map native) w).getD out false = _
  simp [response,computed,run,val,List.foldl_append]

/-- The edited row uses the same operator. The fixed true raw occupies port
zero, with all original wires moved up by one. On the zero assignment the
edited downstream circuit is bounded by its rejecting singleton evaluation. -/
theorem maximum_override {A : Type} (inputs : A → List Bool) (z s : A)
    (pre post : List Raw) (r : Raw) (out : Nat)
    (order : BankLE (inputs z) (inputs s))
    (sz : s ≠ z) (maximum : ∀ a, a ≠ z → computed pre r (inputs a) = true)
    (zeroReject : Circuit.eval ⟨(pre ++ r::post).map native,out⟩ (inputs z) = false)
    (singletonReject : Circuit.eval ⟨(pre ++ r::post).map native,out⟩ (inputs s) = false)
    (a : A) :
    Circuit.eval ⟨(rawEdited pre post r.1).map native,out+1⟩ (true::inputs a) =
      Circuit.eval ⟨(pre ++ r::post).map native,out⟩ (inputs a) := by
  rw [edit_raw_correct, eval_edited, eval_original]
  apply T2RawReader.force_maximum z s (fun v => computed pre r (inputs v))
    (fun v b => response pre post out (inputs v) b) maximum sz
  · simpa only [eval_original] using zeroReject
  · simpa only [eval_original] using singletonReject
  · exact (run_mono post ((run_mono pre order).push (fun h => h))).get out

#print axioms maximum_override
end T2PhysicalMaximum
