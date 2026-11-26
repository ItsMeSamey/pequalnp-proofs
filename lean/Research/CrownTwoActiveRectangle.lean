import Research.TrueOrCount

namespace CrownTwoActiveRectangle
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Research.MissingCell

/-- Two depth-two OR trees group four distinct row labels and four distinct column
labels, using disjoint labels on the diagonal. Their AND computes a 4 by 4 rectangle. -/
def rectangle : Circuit := ⟨[
    ⟨.or,[0,1]⟩, ⟨.or,[2,3]⟩, ⟨.or,[24,25]⟩,
    ⟨.or,[16,17]⟩, ⟨.or,[18,19]⟩, ⟨.or,[27,28]⟩,
    ⟨.and,[26,29]⟩],30⟩

theorem two_active : ∀ i : Fin 12,
    (trueOrFlags rectangle.gates (oneEach i i)).count true ≤ 2 := by decide

theorem computed_rectangle :
    Represents (fun u v : Fin 12 => decide (u.val < 4 ∧ 4 ≤ v.val ∧ v.val < 8)) rectangle := by
  decide

theorem sole_and : Monotone2 rectangle ∧ rectangle.gates.length = 7 ∧
    (rectangle.gates.filter (fun g => match g.op with | .and => true | _ => false)).length = 1 := by
  constructor
  · simp [Monotone2,rectangle]
  · decide

theorem sixteen_cells :
    (Finset.univ.filter (fun p : Fin 12 × Fin 12 =>
      rectangle.eval (oneEach p.1 p.2))).card = 16 := by
  have hc : (Finset.univ.filter (fun p : Fin 12 × Fin 12 =>
      decide (p.1.val < 4 ∧ 4 ≤ p.2.val ∧ p.2.val < 8))).card = 16 := by decide
  have eq : (fun p : Fin 12 × Fin 12 => rectangle.eval (oneEach p.1 p.2)) =
      (fun p => decide (p.1.val < 4 ∧ 4 ≤ p.2.val ∧ p.2.val < 8)) :=
    funext fun p => computed_rectangle p.1 p.2
  exact (congrArg (fun (f : Fin 12 × Fin 12 → Bool) =>
    (Finset.univ.filter (fun p => f p = true)).card) eq).trans hc

theorem diagonal_free : ∀ i : Fin 12, rectangle.eval (oneEach i i) = false := by
  intro i
  rw [computed_rectangle i i]
  simp
  omega

end CrownTwoActiveRectangle
