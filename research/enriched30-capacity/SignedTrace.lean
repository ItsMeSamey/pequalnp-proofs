import PEqualNP.Defs.CircuitLowerBounds
import Mathlib.Data.List.GetD

namespace SignedTrace.Expression

/-- Unfold only the live input-pin occurrences of a designated wire. -/
inductive Expr (ι : Type) where
  | input (i : ι)
  | lit (b : Bool)
  | conj (a b : Expr ι)
  | disj (a b : Expr ι)
  | neg (a : Expr ι)

variable {ι : Type}

def val (x : ι → Bool) : Expr ι → Bool
  | .input i => x i
  | .lit b => b
  | .conj a b => val x a && val x b
  | .disj a b => val x a || val x b
  | .neg a => !(val x a)

/-- false = even sign, true = odd sign. The two disjuncts index the two pins. -/
def path (d : ι) (odd : Bool) : Expr ι → Prop
  | .input i => i = d ∧ odd = false
  | .lit _ => False
  | .conj a b => path d odd a ∨ path d odd b
  | .disj a b => path d odd a ∨ path d odd b
  | .neg a => path d (!odd) a

/-- x reads true and y reads false at the root. Trace the discrepancy to an
input, keeping its polarity. No promise that intermediate assignments are on care. -/
theorem trace (e : Expr ι) : ∀ (x y : ι → Bool), val x e = true →
    val y e = false → ∃ i, (path i false e ∧ x i = true ∧ y i = false) ∨
                            (path i true e ∧ x i = false ∧ y i = true) := by
  induction e with
  | input i =>
      intro x y hx hy
      exact ⟨i, Or.inl ⟨⟨rfl, rfl⟩, hx, hy⟩⟩
  | lit b =>
      intro x y hx hy
      change b = true at hx
      change b = false at hy
      simp_all
  | conj a b ia ib =>
      intro x y hx hy
      have xa : val x a = true := by cases h : val x a <;> simp_all [val]
      have xb : val x b = true := by cases h : val x b <;> simp_all [val]
      by_cases h : val y a = false
      · obtain ⟨i, hi⟩ := ia x y xa h
        refine ⟨i, ?_⟩
        rcases hi with ⟨p,u,v⟩ | ⟨p,u,v⟩
        · exact Or.inl ⟨Or.inl p,u,v⟩
        · exact Or.inr ⟨Or.inl p,u,v⟩
      · have yb : val y b = false := by
          cases ha : val y a <;> cases hb : val y b <;> simp_all [val]
        obtain ⟨i, hi⟩ := ib x y xb yb
        refine ⟨i, ?_⟩
        rcases hi with ⟨p,u,v⟩ | ⟨p,u,v⟩
        · exact Or.inl ⟨Or.inr p,u,v⟩
        · exact Or.inr ⟨Or.inr p,u,v⟩
  | disj a b ia ib =>
      intro x y hx hy
      have ya : val y a = false := by cases h : val y a <;> simp_all [val]
      have yb : val y b = false := by cases h : val y b <;> simp_all [val]
      by_cases h : val x a = true
      · obtain ⟨i, hi⟩ := ia x y h ya
        refine ⟨i, ?_⟩
        rcases hi with ⟨p,u,v⟩ | ⟨p,u,v⟩
        · exact Or.inl ⟨Or.inl p,u,v⟩
        · exact Or.inr ⟨Or.inl p,u,v⟩
      · have xb : val x b = true := by
          cases ha : val x a <;> cases hb : val x b <;> simp_all [val]
        obtain ⟨i, hi⟩ := ib x y xb yb
        refine ⟨i, ?_⟩
        rcases hi with ⟨p,u,v⟩ | ⟨p,u,v⟩
        · exact Or.inl ⟨Or.inr p,u,v⟩
        · exact Or.inr ⟨Or.inr p,u,v⟩
  | neg a ih =>
      intro x y hx hy
      have ax : val x a = false := by cases h : val x a <;> simp_all [val]
      have ay : val y a = true := by cases h : val y a <;> simp_all [val]
      obtain ⟨i, hi⟩ := ih y x ay ax
      refine ⟨i, ?_⟩
      rcases hi with ⟨p,u,v⟩ | ⟨p,u,v⟩
      · exact Or.inr ⟨p,v,u⟩
      · exact Or.inl ⟨p,v,u⟩

/-- A comparable falling pair forces odd parity for some increasing input.
The order assumption applies to every exposed input, including aliases. -/
theorem comparable_fall (e : Expr ι) (x y : ι → Bool)
    (hxy : ∀ i, x i = true → y i = true)
    (hx : val x e = true) (hy : val y e = false) :
    ∃ i, path i true e ∧ x i = false ∧ y i = true := by
  obtain ⟨i, h⟩ := trace e x y hx hy
  rcases h with ⟨_, u, v⟩ | h
  · have z := hxy i u
    simp_all
  · exact ⟨i, h⟩

/-- A rising and a falling essential edge for this same donor. The other
inputs may have different fixed values in the two witness pairs. -/
theorem both_signs (e : Expr ι) (d : ι) (r0 r1 f0 f1 : ι → Bool)
    (hr : ∀ i, i ≠ d → r0 i = r1 i) (hf : ∀ i, i ≠ d → f0 i = f1 i)
    (rd0 : r0 d = false) (rd1 : r1 d = true)
    (fd0 : f0 d = false) (fd1 : f1 d = true)
    (rv0 : val r0 e = false) (rv1 : val r1 e = true)
    (fv0 : val f0 e = true) (fv1 : val f1 e = false) :
    path d false e ∧ path d true e := by
  constructor
  · obtain ⟨i, h⟩ := trace e r1 r0 rv1 rv0
    by_cases hi : i = d
    · subst i
      rcases h with ⟨p,_,_⟩ | ⟨_,u,_⟩
      · exact p
      · simp_all
    · have eq := hr i hi
      rcases h with ⟨_,u,v⟩ | ⟨_,u,v⟩ <;> simp_all
  · obtain ⟨i, h⟩ := trace e f0 f1 fv0 fv1
    by_cases hi : i = d
    · subst i
      rcases h with ⟨_,u,_⟩ | ⟨p,_,_⟩
      · simp_all
      · exact p
    · have eq := hf i hi
      rcases h with ⟨_,u,v⟩ | ⟨_,u,v⟩ <;> simp_all

end SignedTrace.Expression
namespace SignedTrace.Gates
open SignedTrace.Expression PEqualNP.CircuitLowerBounds

abbrev Good (g : Gate) := g.op = .and ∨ g.op = .or ∨ g.op = .not

def expand (g : Gate) (read : Nat → Expr Nat) : Expr Nat :=
  match g.op with
  | .and => (g.inputs.map read).foldr Expr.conj (.lit true)
  | .or => (g.inputs.map read).foldr Expr.disj (.lit false)
  | .not => .neg ((g.inputs.map read).headD (.lit false))
  | _ => .lit false

/-- Each lookup is a closure over strictly earlier gates. Nothing caches an
unfolded wire and repeated lookups independently unfold both pin occurrences. -/
def finish : List Gate → Nat → (Nat → Expr Nat) → Nat → Expr Nat
  | [], _, read => read
  | g :: gs, n, read => finish gs (n+1) (fun i => if i=n then expand g read else read i)

def unfoldOutput (C : Circuit) (n : Nat) : Expr Nat :=
  finish C.gates n (fun i => if i<n then .input i else .lit false) C.output

private theorem val_and (x : Nat → Bool) (es : List (Expr Nat)) :
    val x (es.foldr Expr.conj (.lit true)) = (es.map (val x)).all id := by
  induction es with
  | nil => rfl
  | cons a as ih => simp [val, ih]

private theorem val_or (x : Nat → Bool) (es : List (Expr Nat)) :
    val x (es.foldr Expr.disj (.lit false)) = (es.map (val x)).any id := by
  induction es with
  | nil => rfl
  | cons a as ih => simp [val, ih]

private theorem val_head (x : Nat → Bool) (es : List (Expr Nat)) :
    val x (es.headD (.lit false)) = (es.map (val x)).headD false := by
  cases es <;> rfl

theorem expand_sound (g : Gate) (hg : Good g) (read : Nat → Expr Nat) (x : Nat → Bool) :
    val x (expand g read) = g.op.eval (g.inputs.map fun i => val x (read i)) := by
  rcases hg with h | h | h
  · simp [expand, h, GateOp.eval, val_and, List.map_map, Function.comp_def]
  · simp [expand, h, GateOp.eval, val_or, List.map_map, Function.comp_def]
  · cases hi : g.inputs <;> simp [expand, h, hi, GateOp.eval, val]

/-- Local transfer to an actual operand position. Fin indexes the pin list,
so two equal wire IDs retain distinct positions. NOT consults only pin zero. -/
private theorem fold_and_path (d : Nat) (odd : Bool) (es : List (Expr Nat)) :
    path d odd (es.foldr Expr.conj (.lit true)) ↔ ∃ e ∈ es, path d odd e := by
  induction es with
  | nil => simp [path]
  | cons e es ih => simp [path, ih]

private theorem fold_or_path (d : Nat) (odd : Bool) (es : List (Expr Nat)) :
    path d odd (es.foldr Expr.disj (.lit false)) ↔ ∃ e ∈ es, path d odd e := by
  induction es with
  | nil => simp [path]
  | cons e es ih => simp [path, ih]

theorem binary_pin_path (g : Gate) (read : Nat → Expr Nat) (d : Nat) (odd : Bool)
    (hg : g.op = .and ∨ g.op = .or) :
    path d odd (expand g read) ↔ ∃ j : Fin g.inputs.length, path d odd (read (g.inputs.get j)) := by
  have member : (∃ e ∈ g.inputs.map read, path d odd e) ↔
      ∃ j : Fin g.inputs.length, path d odd (read (g.inputs.get j)) := by
    constructor
    · rintro ⟨e, h, hp⟩
      obtain ⟨wire, hw, rfl⟩ := List.mem_map.mp h
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hw
      exact ⟨i, by simpa only [hi] using hp⟩
    · rintro ⟨j,hj⟩
      exact ⟨_, List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩, hj⟩
  rcases hg with h | h
  · simpa only [expand,h,fold_and_path] using member
  · simpa only [expand,h,fold_or_path] using member

theorem neg_pin_path (g : Gate) (read : Nat → Expr Nat) (d : Nat) (odd : Bool)
    (hg : g.op = .not) :
    path d odd (expand g read) ↔
      match g.inputs with
      | [] => False
      | pin :: _ => path d (!odd) (read pin) := by
  cases h : g.inputs <;> simp [expand,hg,h,path]

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem last_read (w : List Bool) (b : Bool) (i : Nat) :
    (w ++ [b]).getD i false = if i=w.length then b else w.getD i false := by
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h, if_neg (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases e : i=w.length
    · subst i; simp
    · rw [if_neg e, List.getD_eq_default _ _ (by omega : w.length ≤ i),
          List.getD_eq_default _ _ (by simpa using (show 1 ≤ i-w.length by omega))]

theorem finish_sound (gs : List Gate) (x : Nat → Bool) (w : List Bool)
    (read : Nat → Expr Nat) (hg : ∀ g ∈ gs, Good g)
    (hr : ∀ i, val x (read i) = w.getD i false) (out : Nat) :
    val x (finish gs w.length read out) = (gs.foldl step w).getD out false := by
  induction gs generalizing w read with
  | nil => exact hr out
  | cons g gs ih =>
      let next := fun i => if i=w.length then expand g read else read i
      have same : ∀ i, val x (next i) = (step w g).getD i false := by
        intro i
        rw [step, last_read]
        by_cases e : i=w.length
        · subst i
          simp [next, expand_sound g (hg g (by simp)), hr]
        · simpa [next,e] using hr i
      have tail := ih (w := step w g) (read := next) (fun a ha => hg a (by simp [ha])) same
      simpa [finish, step, next] using tail

theorem syntax_sound (C : Circuit) (bits : List Bool) (hg : ∀ g ∈ C.gates, Good g) :
    val (fun i => bits.getD i false) (unfoldOutput C bits.length) = C.eval bits := by
  unfold unfoldOutput Circuit.eval Circuit.wires
  apply finish_sound C.gates _ bits _ hg
  intro i
  split_ifs with h
  · rfl
  · exact (List.getD_eq_default bits false (by omega : bits.length ≤ i)).symm

/-- End-to-end discrepancy witness for two equal-width evaluations of the
actual gate list. The path proof is over its pin-occurrence unfolding. -/
theorem circuit_trace (C : Circuit) (x y : List Bool) (hlen : y.length=x.length)
    (hg : ∀ g ∈ C.gates, Good g) (hx : C.eval x=true) (hy : C.eval y=false) :
    ∃ i, (path i false (unfoldOutput C x.length) ∧ x.getD i false=true ∧ y.getD i false=false) ∨
         (path i true (unfoldOutput C x.length) ∧ x.getD i false=false ∧ y.getD i false=true) := by
  apply trace (unfoldOutput C x.length) (fun i => x.getD i false) (fun i => y.getD i false)
  · exact (syntax_sound C x hg).trans hx
  · rw [←hlen, syntax_sound C y hg]
    exact hy


/-- Falling comparable physical inputs force an odd occurrence path from an
input that rose. Both lists describe the same number of physical inputs. -/
theorem circuit_comparable_fall (C : Circuit) (x y : List Bool)
    (hlen : y.length = x.length) (hg : ∀ g ∈ C.gates, Good g)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true)
    (hx : C.eval x = true) (hy : C.eval y = false) :
    ∃ i, path i true (unfoldOutput C x.length) ∧
      x.getD i false = false ∧ y.getD i false = true := by
  obtain ⟨i, hi⟩ := circuit_trace C x y hlen hg hx hy
  rcases hi with ⟨_, xi, yi⟩ | hi
  · have impossible := hxy i xi
    rw [yi] at impossible
    cases impossible
  · exact ⟨i, hi⟩

/-- A rising and a falling essential edge for one physical donor force
opposite parities, even when the two pairs use different backgrounds. -/
theorem circuit_both_signs (C : Circuit) (n d : Nat) (r0 r1 f0 f1 : List Bool)
    (hg : ∀ g ∈ C.gates, Good g)
    (lr0 : r0.length = n) (lr1 : r1.length = n)
    (lf0 : f0.length = n) (lf1 : f1.length = n)
    (hr : ∀ i, i ≠ d → r0.getD i false = r1.getD i false)
    (hf : ∀ i, i ≠ d → f0.getD i false = f1.getD i false)
    (rd0 : r0.getD d false = false) (rd1 : r1.getD d false = true)
    (fd0 : f0.getD d false = false) (fd1 : f1.getD d false = true)
    (rv0 : C.eval r0 = false) (rv1 : C.eval r1 = true)
    (fv0 : C.eval f0 = true) (fv1 : C.eval f1 = false) :
    path d false (unfoldOutput C n) ∧ path d true (unfoldOutput C n) := by
  apply both_signs (unfoldOutput C n) d
    (fun i => r0.getD i false) (fun i => r1.getD i false)
    (fun i => f0.getD i false) (fun i => f1.getD i false)
    hr hf rd0 rd1 fd0 fd1
  · simpa only [lr0] using (syntax_sound C r0 hg).trans rv0
  · simpa only [lr1] using (syntax_sound C r1 hg).trans rv1
  · simpa only [lf0] using (syntax_sound C f0 hg).trans fv0
  · simpa only [lf1] using (syntax_sound C f1 hg).trans fv1

end SignedTrace.Gates
