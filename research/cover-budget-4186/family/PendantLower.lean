import PEqualNP.MetaComplexity.Helpers.Elim
import PEqualNP.MetaComplexity.Helpers.ExactMaj3

namespace PendantLower4186

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

/-- Setting the last input to false repeatedly leaves majority on three inputs. -/
def chain : (k : ℕ) → (((Fin (3 + k) → Bool) → Bool) → Prop)
  | 0, f => f = ExactMaj3.maj3
  | k + 1, f =>
      (∃ x : Fin ((3 + k) + 1) → Bool,
        f (Function.update x (Fin.last (3 + k)) (!x (Fin.last (3 + k)))) ≠ f x) ∧
      (∃ y y' : Fin (3 + k) → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc y' false)) ∧
      chain k (fun y => f (Fin.snoc y false))

theorem lower (k : ℕ) (f : (Fin (3 + k) → Bool) → Bool) (hc : chain k f) :
    ¬ HasCircuitSize (3 + k) f (3 + k) := by
  induction k with
  | zero =>
    change f = ExactMaj3.maj3 at hc
    subst f
    exact ExactMaj3.maj3_lower
  | succ k ih =>
    obtain ⟨hdep, hnc, hrest⟩ := hc
    intro h
    exact ih _ hrest (gate_elim (3 + k) f false (3 + k) hdep hnc h)

end PendantLower4186
