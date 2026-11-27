import PEqualNP.Defs

/-! The expression compiler and its simulation proof below are adapted from
PEqualNP/Library/Helpers/TableauExpr.lean (Apache-2.0, open-goat/pequalnp-proofs).
Only the compiler prefix and its semantic contract are needed here. -/
namespace OnePerShore.Upper.Compiler

open PEqualNP.CircuitLowerBounds

/-- Formulas. -/
inductive Ex (α : Type) where
  | var : α → Ex α
  | const : Bool → Ex α
  | not : Ex α → Ex α
  | and : Ex α → Ex α → Ex α
  | or : Ex α → Ex α → Ex α

namespace Ex

variable {α β : Type}

/-- Value of a formula. -/
def eval (ρ : α → Bool) : Ex α → Bool
  | var a => ρ a
  | const b => b
  | not e => !(eval ρ e)
  | and e f => eval ρ e && eval ρ f
  | or e f => eval ρ e || eval ρ f

/-- Number of nodes. -/
def size : Ex α → ℕ
  | var _ => 1
  | const _ => 1
  | not e => size e + 1
  | and e f => size e + size f + 1
  | or e f => size e + size f + 1

/-- Substitution. -/
def bind (σ : α → Ex β) : Ex α → Ex β
  | var a => σ a
  | const b => const b
  | not e => not (bind σ e)
  | and e f => and (bind σ e) (bind σ f)
  | or e f => or (bind σ e) (bind σ f)

theorem eval_bind (ρ : β → Bool) (σ : α → Ex β) (e : Ex α) :
    eval ρ (bind σ e) = eval (fun a => eval ρ (σ a)) e := by
  induction e with
  | var a => rfl
  | const b => rfl
  | not e ih => simp [bind, eval, ih]
  | and e f ih1 ih2 => simp [bind, eval, ih1, ih2]
  | or e f ih1 ih2 => simp [bind, eval, ih1, ih2]

theorem size_bind (σ : α → Ex β) (hσ : ∀ a, size (σ a) = 1) (e : Ex α) :
    size (bind σ e) = size e := by
  induction e with
  | var a => exact hσ a
  | const b => rfl
  | not e ih => simp [bind, size, ih]
  | and e f ih1 ih2 => simp [bind, size, ih1, ih2]
  | or e f ih1 ih2 => simp [bind, size, ih1, ih2]

end Ex

open Ex

/-! ## Wires -/

/-- All wires after running a gate list on the wire list `W`. -/
def run (gs : List Gate) (W : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W

theorem run_wires (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (gs gs' : List Gate) (W : List Bool) :
    run (gs ++ gs') W = run gs' (run gs W) := by
  simp [run, List.foldl_append]

theorem run_nil (W : List Bool) : run [] W = W := rfl

theorem run_single (g : Gate) (W : List Bool) :
    run [g] W = W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)] := rfl

theorem run_prefix (gs : List Gate) : ∀ W : List Bool, ∃ t, run gs W = W ++ t := by
  induction gs with
  | nil => intro W; exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    intro W
    obtain ⟨t, ht⟩ := ih (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => W.getD i false)] ++ t, ?_⟩
    change run gs _ = _
    rw [ht, List.append_assoc]

theorem length_run (gs : List Gate) : ∀ W : List Bool, (run gs W).length = W.length + gs.length := by
  induction gs with
  | nil => intro W; simp [run]
  | cons g gs ih =>
    intro W
    change (run gs _).length = _
    rw [ih]; simp; omega

theorem getD_run (gs : List Gate) (W : List Bool) (i : ℕ) (h : i < W.length) :
    (run gs W).getD i false = W.getD i false := by
  obtain ⟨t, ht⟩ := run_prefix gs W
  rw [ht, List.getD_append _ _ _ _ h]

/-- `W` carries `ρ` on the wires `w`. -/
def Rep {α : Type} (W : List Bool) (w : α → ℕ) (ρ : α → Bool) : Prop :=
  ∀ a, w a < W.length ∧ W.getD (w a) false = ρ a

theorem rep_run {α : Type} {W : List Bool} {w : α → ℕ} {ρ : α → Bool} (h : Rep W w ρ)
    (gs : List Gate) : Rep (run gs W) w ρ := by
  intro a
  refine ⟨?_, ?_⟩
  · rw [length_run]; have := (h a).1; omega
  · rw [getD_run _ _ _ (h a).1]; exact (h a).2

/-- A gate allowed in `SIZE`. -/
def Basic (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

/-! ## Compiling one formula -/

section compile

variable {α : Type} (w : α → ℕ)

/-- The gates of a formula appended after `N` wires, and its output wire. -/
def compile : Ex α → ℕ → List Gate × ℕ
  | .var a, _ => ([], w a)
  | .const b, N => ([⟨if b then GateOp.and else GateOp.or, []⟩], N)
  | .not e, N =>
    let p := compile e N
    (p.1 ++ [⟨GateOp.not, [p.2]⟩], N + p.1.length)
  | .and e f, N =>
    let p := compile e N
    let q := compile f (N + p.1.length)
    (p.1 ++ q.1 ++ [⟨GateOp.and, [p.2, q.2]⟩], N + p.1.length + q.1.length)
  | .or e f, N =>
    let p := compile e N
    let q := compile f (N + p.1.length)
    (p.1 ++ q.1 ++ [⟨GateOp.or, [p.2, q.2]⟩], N + p.1.length + q.1.length)

theorem compile_basic : ∀ (e : Ex α) (N : ℕ), ∀ g ∈ (compile w e N).1, Basic g
  | .var a, N => by simp [compile]
  | .const b, N => by
    intro g hg
    simp only [compile, List.mem_singleton] at hg
    subst hg
    cases b <;> simp [Basic]
  | .not e, N => by
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact compile_basic e N g hg
    · subst hg; simp [Basic]
  | .and e f, N => by
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact compile_basic e N g hg
    · exact compile_basic f _ g hg
    · subst hg; simp [Basic]
  | .or e f, N => by
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact compile_basic e N g hg
    · exact compile_basic f _ g hg
    · subst hg; simp [Basic]

theorem compile_length : ∀ (e : Ex α) (N : ℕ), (compile w e N).1.length ≤ size e
  | .var a, N => by simp [compile, size]
  | .const b, N => by simp [compile, size]
  | .not e, N => by
    have := compile_length e N
    simp only [compile, size, List.length_append, List.length_singleton]; omega
  | .and e f, N => by
    have := compile_length e N
    have := compile_length f (N + (compile w e N).1.length)
    simp only [compile, size, List.length_append, List.length_singleton]; omega
  | .or e f, N => by
    have := compile_length e N
    have := compile_length f (N + (compile w e N).1.length)
    simp only [compile, size, List.length_append, List.length_singleton]; omega

theorem getD_snoc_len (W : List Bool) (b : Bool) : (W ++ [b]).getD W.length false = b := by
  simp

theorem compile_spec : ∀ (e : Ex α) (W : List Bool) (ρ : α → Bool), Rep W w ρ →
    (compile w e W.length).2 < W.length + (compile w e W.length).1.length ∧
    (run (compile w e W.length).1 W).getD (compile w e W.length).2 false = eval ρ e
  | .var a, W, ρ, h => by
    simp only [compile, List.length_nil, Nat.add_zero, run_nil, eval]
    exact h a
  | .const b, W, ρ, h => by
    simp only [compile, List.length_singleton, run_single, eval]
    refine ⟨by omega, ?_⟩
    rw [getD_snoc_len]
    cases b <;> simp [GateOp.eval]
  | .not e, W, ρ, h => by
    obtain ⟨h1, h2⟩ := compile_spec e W ρ h
    simp only [compile, List.length_append, List.length_singleton, run_append, run_single,
      eval]
    refine ⟨by omega, ?_⟩
    have hl := length_run (compile w e W.length).1 W
    rw [← hl, getD_snoc_len]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
    exact congrArg _ h2
  | .and e f, W, ρ, h => by
    obtain ⟨h1, h2⟩ := compile_spec e W ρ h
    set p := compile w e W.length
    have hl := length_run p.1 W
    have h' := rep_run h p.1
    obtain ⟨h3, h4⟩ := compile_spec f (run p.1 W) ρ h'
    rw [hl] at h3 h4
    simp only [compile, List.length_append, List.length_singleton, run_append, run_single,
      eval]
    refine ⟨by omega, ?_⟩
    set q := compile w f (W.length + p.1.length)
    have hl2 := length_run q.1 (run p.1 W)
    rw [hl] at hl2
    have e1 : W.length + p.1.length + q.1.length = (run q.1 (run p.1 W)).length := by
      rw [hl2]
    rw [e1, getD_snoc_len]
    have e2 : (run q.1 (run p.1 W)).getD p.2 false = eval ρ e := by
      rw [getD_run _ _ _ (by rw [hl]; omega), h2]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
      Bool.and_true]
    exact congrArg₂ _ e2 h4
  | .or e f, W, ρ, h => by
    obtain ⟨h1, h2⟩ := compile_spec e W ρ h
    set p := compile w e W.length
    have hl := length_run p.1 W
    have h' := rep_run h p.1
    obtain ⟨h3, h4⟩ := compile_spec f (run p.1 W) ρ h'
    rw [hl] at h3 h4
    simp only [compile, List.length_append, List.length_singleton, run_append, run_single,
      eval]
    refine ⟨by omega, ?_⟩
    set q := compile w f (W.length + p.1.length)
    have hl2 := length_run q.1 (run p.1 W)
    rw [hl] at hl2
    have e1 : W.length + p.1.length + q.1.length = (run q.1 (run p.1 W)).length := by
      rw [hl2]
    rw [e1, getD_snoc_len]
    have e2 : (run q.1 (run p.1 W)).getD p.2 false = eval ρ e := by
      rw [getD_run _ _ _ (by rw [hl]; omega), h2]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
      Bool.or_false]
    exact congrArg₂ _ e2 h4

end compile
end OnePerShore.Upper.Compiler
