import PhysicalReadOnce
import ReadOnceP4

namespace OnePerShore

abbrev Four := Bool → Bool → Bool → Bool → Bool

def Corner (f : Four) : Prop :=
  f true false false false = false ∧ f false true false false = false ∧
  f false false true false = false ∧ f false false false true = false ∧
  f true false true false = true ∧ f true false false true = true ∧
  f false true true false = true ∧ f false true false true = false

/-- Closure of the obstruction under a root split, including an empty
projected child. The nonempty case is the finite four-variable lemma. -/
private theorem no_corner_split (op a b c d : Bool) (f g : Four)
    (fz : f false false false false = false) (gz : g false false false false = false)
    (hf : ¬ Corner f) (hg : ¬ Corner g) :
    ¬ Corner (ReadOnceP4.rootValue op a b c d f g) := by
  by_cases hl : a || b || c || d = true
  · by_cases hr : !a || !b || !c || !d = true
    · rintro ⟨sx,sy,sz,sw,xz,xw,yz,yw⟩
      exact ReadOnceP4.no_split op a b c d f g hl hr fz gz sx sy sz sw xz xw yz yw
    · cases a <;> cases b <;> cases c <;> cases d <;> cases op <;>
        simp_all [Corner, ReadOnceP4.rootValue]
  · cases a <;> cases b <;> cases c <;> cases d <;> cases op <;>
      simp_all [Corner, ReadOnceP4.rootValue]

def paint (a b c d : ℕ) (x y z w : Bool) (i : ℕ) : Bool :=
  (decide (i=a) && x) || (decide (i=b) && y) ||
  (decide (i=c) && z) || (decide (i=d) && w)

def Formula.trace (t : Formula) (a b c d : ℕ) : Four :=
  fun x y z w => t.eval (paint a b c d x y z w)

theorem Formula.eval_congr (t : Formula) (x y : ℕ → Bool)
    (h : ∀ i ∈ t.leaves, x i = y i) : t.eval x = t.eval y := by
  induction t with
  | atom i => exact h i (by simp [Formula.leaves])
  | node op l r il ir =>
    simp only [Formula.eval]
    rw [il (fun i hi => h i (by simp [Formula.leaves,hi])),
        ir (fun i hi => h i (by simp [Formula.leaves,hi]))]

theorem Formula.eval_zero (t : Formula) : t.eval (fun _ => false) = false := by
  induction t <;> simp_all [Formula.eval]

private theorem trace_zero (t : Formula) (a b c d : ℕ) :
    t.trace a b c d false false false false = false := by
  change t.eval (paint a b c d false false false false) = false
  rw [t.eval_congr _ (fun _ => false) (fun i _ => by simp [paint])]
  exact t.eval_zero

private theorem trace_mask (t : Formula) (a b c d : ℕ) (p : ℕ → Bool)
    (hp : ∀ i ∈ t.leaves, p i = true) (x y z w : Bool) :
    t.trace a b c d (p a && x) (p b && y) (p c && z) (p d && w) =
    t.trace a b c d x y z w := by
  apply Formula.eval_congr
  intro i hi
  have h := hp i hi
  by_cases ha : i=a <;> by_cases hb : i=b <;> by_cases hc : i=c <;> by_cases hd : i=d <;>
    simp_all [paint]

theorem Formula.no_corner (t : Formula) (nd : t.leaves.Nodup) (a b c d : ℕ) :
    ¬ Corner (t.trace a b c d) := by
  induction t with
  | atom i =>
    by_cases ha : i=a <;> by_cases hb : i=b <;> by_cases hc : i=c <;> by_cases hd : i=d <;>
      simp [Corner,Formula.trace,Formula.eval,paint,ha,hb,hc,hd]
  | node op l r ihl ihr =>
    obtain ⟨nl,nr,apart⟩ := List.nodup_append'.mp nd
    let p := fun i : ℕ => decide (i ∈ l.leaves)
    have hl : ∀ i ∈ l.leaves, p i = true := fun i hi => by simp [p,hi]
    have hr : ∀ i ∈ r.leaves, !(p i) = true := by
      intro i hi
      have hn : i ∉ l.leaves := fun h => (List.disjoint_left.mp apart) h hi
      simp [p,hn]
    have e : ReadOnceP4.rootValue op (p a) (p b) (p c) (p d)
        (l.trace a b c d) (r.trace a b c d) = (Formula.node op l r).trace a b c d := by
      funext x y z w
      unfold ReadOnceP4.rootValue
      rw [trace_mask l a b c d p hl,
        trace_mask r a b c d (fun i => !(p i)) hr]
      rfl
    rw [←e]
    exact no_corner_split op _ _ _ _ _ _ (trace_zero ..) (trace_zero ..) (ihl nl) (ihr nr)

end OnePerShore
