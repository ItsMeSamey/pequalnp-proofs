import Research.TrueOrCount

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def chain {X : Type*} (raw first z : Set X) : Prop :=
  z = raw ∨ z = first ∨ z = Set.univ

private theorem chain_inter {X : Type*} {raw first a b : Set X} (le : raw ⊆ first)
    (ha : chain raw first a) (hb : chain raw first b) : chain raw first (a ∩ b) := by
  rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl <;>
    simp [chain,Set.inter_eq_left.mpr le,Set.inter_eq_right.mpr le]

private def truthWire {X : Type*} (w : X → List Bool) (i : Nat) : Set X :=
  {q | (w q).getD i false = true}

private def truthAnd {X : Type*} (w : X → List Bool) (ls : List Nat) : Set X :=
  {q | ∀ i ∈ ls, q ∈ truthWire w i}

private theorem and_chain {X : Type*} {raw first : Set X} (w : X → List Bool) (p : X)
    (le : raw ⊆ first) (inv : ∀ i, p ∈ truthWire w i → chain raw first (truthWire w i))
    (ls : List Nat) (hp : p ∈ truthAnd w ls) : chain raw first (truthAnd w ls) := by
  induction ls with
  | nil => exact Or.inr (Or.inr (by ext; simp [truthAnd]))
  | cons i ls ih =>
    have lhs : truthAnd w (i::ls) = truthWire w i ∩ truthAnd w ls := by ext; simp [truthAnd]
    rw [lhs] at hp ⊢
    exact chain_inter le (inv i hp.1) (ih hp.2)

/-- With only one OR function active at the distinguished input, every true wire of
the entire prefix computes the active literal, the OR function, or true. -/
theorem prefix_one_or_chain {X : Type*} (gs : List Gate) (w : X → List Bool) (p : X)
    (raw first : Set X) (le : raw ⊆ first) (len : ∀ q, (w q).length = (w p).length)
    (base : ∀ i, (w p).getD i false = true →
      {q | (w q).getD i false = true} = raw ∨
      {q | (w q).getD i false = true} = first ∨ {q | (w q).getD i false = true} = Set.univ)
    (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (exceptional : ∀ i, (trueOrFlags gs (w p)).getD i false = true →
      {q | (trueOrFlags gs (w q)).getD i false = true} = first) :
    ∀ i, ((Circuit.mk gs 0).wires (w p)).getD i false = true →
      {q | ((Circuit.mk gs 0).wires (w q)).getD i false = true} = raw ∨
      {q | ((Circuit.mk gs 0).wires (w q)).getD i false = true} = first ∨
      {q | ((Circuit.mk gs 0).wires (w q)).getD i false = true} = Set.univ := by
  induction gs generalizing w with
  | nil => exact base
  | cons g gs ih =>
    apply ih (fun q => advance g (w q)) (fun q => by simp [advance_len,len q]) _
      (fun g' hg => mono g' (List.mem_cons_of_mem _ hg)) (fun i => exceptional (i+1))
    intro i on
    by_cases hi : i < (w p).length
    · have old (q : X) := getD_advance_lt g (w q) i (by rw [len]; exact hi)
      simp only [old] at on ⊢
      exact base i on
    · by_cases he : i = (w p).length
      · subst i
        have val (q : X) : (advance g (w q)).getD (w p).length false =
            g.op.eval (g.inputs.map fun i => (w q).getD i false) := by
          rw [← len q]; exact getD_advance_eq ..
        simp only [val] at on ⊢
        rcases mono g (List.mem_cons_self ..) with ha|ho
        · have eq : {q | g.op.eval (g.inputs.map fun i => (w q).getD i false) = true} =
              truthAnd w g.inputs := by ext; simp [ha,GateOp.eval,truthAnd,truthWire,List.all_map]
          rw [eq]
          apply and_chain w p le base
          rw [← eq]; exact on
        · apply Or.inr; apply Or.inl
          have firstFlag (q : X) : (trueOrFlags (g::gs) (w q)).getD 0 false =
              g.op.eval (g.inputs.map fun i => (w q).getD i false) := by
            change (isOrGate g && _) = _
            simp [isOrGate,ho]
          simpa only [firstFlag] using (exceptional 0 ((firstFlag p).trans on))
      · rw [getD_missing (by rw [advance_len]; omega : (advance g (w p)).length ≤ i)] at on
        contradiction

end PEqualNP.Research.MissingCell
