import Mathlib.Tactic.Linarith

namespace OneJoinPortBudget

/-- Two dirty exits of positive singleton support can save at most three
raw-occurrence payments at one nonraw join. -/
theorem outsideJoinDiscount (h₁ h₂ : ℤ) (h₁pos : 1 ≤ h₁) (h₂pos : 1 ≤ h₂) :
    max 0 (3 - h₁) + max 0 (3 - h₂) - max 0 (3 - (h₁ + h₂)) ≤ 3 := by
  rcases le_total 0 (3 - h₁) with ha | ha <;>
    rcases le_total 0 (3 - h₂) with hb | hb <;>
    rcases le_total 0 (3 - (h₁ + h₂)) with hc | hc <;>
    simp_all only [max_eq_right, max_eq_left] <;> omega

/-- Sum the payments to the shared-root trees and to the unused branch
and dirty exits in the five-pure, three-terminal case. -/
theorem fivePurePortSum (R M H J S y z t k e : ℤ)
    (terms : y + z + t = k + 1 - e)
    (payments : M - J - 3 * y - S + (6 - y) + (3 * (4 - z) - (H - S)) -
      3 * e + (1 - e) * max 0 (2 - z) ≤ R) :
    M - H + 14 - 4 * k + 4 * t + z - J + e +
      (1 - e) * max 0 (2 - z) ≤ R := by
  linarith only [terms, payments]

/-- The analogous count with five dirty products and two terminals. -/
theorem fourPurePortSum (R M H J S y z t k e : ℤ)
    (terms : y + z + t = k + 1 - e)
    (payments : M - J - 3 * y - S + (6 - y) + (3 * (5 - z) - (H - S)) -
      3 * e + (1 - e) * max 0 (3 - z) ≤ R) :
    M - H + 17 - 4 * k + 4 * t + z - J + e +
      (1 - e) * max 0 (3 - z) ≤ R := by
  linarith only [terms, payments]

/-- Under the raw budget, two shared ORs force both supports to attain
seven, and the unique nonraw join to be outside their trees. -/
theorem twoRootsEquality (B R A J t z e q : ℤ)
    (budget : R ≤ B) (fanoutCap : A ≤ 7) (parentCap : J ≤ 7 * t)
    (internalCount : 0 ≤ t ∧ t ≤ 1) (dirtyCount : 0 ≤ z)
    (joinLocation : e = 0 ∨ e = 1) (ports : 2 ≤ q)
    (payments : B + 9 - A + 4 * t + z - J + e +
      (1 - e) * max 0 (q - z) ≤ R) :
    e = 1 ∧ t = 1 ∧ z = 0 ∧ A = 7 ∧ J = 7 := by
  have extra : q - z ≤ max 0 (q - z) := le_max_right _ _
  rcases joinLocation with he | he <;> subst e <;> simp at payments <;> omega

/-- For three shared ORs both available internal parent occurrences must
attain seven. The structural chain-or-fork exclusion is a separate input. -/
theorem threeRootsEquality (B R J t z e q : ℤ)
    (budget : R ≤ B) (parentCap : J ≤ 7 * t)
    (internalCount : 0 ≤ t ∧ t ≤ 2) (dirtyCount : 0 ≤ z)
    (joinLocation : e = 0 ∨ e = 1) (ports : 2 ≤ q)
    (payments : B + 5 + 4 * t + z - J + e +
      (1 - e) * max 0 (q - z) ≤ R) :
    e = 1 ∧ t = 2 ∧ z = 0 ∧ J = 14 := by
  have extra : q - z ≤ max 0 (q - z) := le_max_right _ _
  rcases joinLocation with he | he <;> subst e <;> simp at payments <;> omega

end OneJoinPortBudget
