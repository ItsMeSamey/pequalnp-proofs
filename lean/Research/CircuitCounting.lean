import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

namespace CircuitCounting

abbrev Table (n : ℕ) := (Fin n → Bool) → Bool

/-- One output pointer and s labeled gates, each with two source pointers.
The encoding permits unused and invalid descriptions, giving an upper bound. -/
abbrev Code (n s : ℕ) :=
  Fin (n+s+2) × (Fin s → Fin 3 × Fin (n+s+2) × Fin (n+s+2))

theorem code_count (n s : ℕ) :
    Fintype.card (Code n s) = (n+s+2) * (3 * ((n+s+2) * (n+s+2)))^s := by
  simp [Code]

/-- Every semantics for these descriptions misses an entire truth table
whenever descriptions are fewer than tables. -/
theorem missing_table (n s : ℕ) (eval : Code n s → Table n)
    (h : (n+s+2) * (3 * ((n+s+2) * (n+s+2)))^s < 2^(2^n)) :
    ∃ t : Table n, ∀ c : Code n s, ∃ x, eval c x ≠ t x := by
  classical
  by_contra! hall
  have surj : Function.Surjective eval := by
    intro t
    obtain ⟨c, hc⟩ := hall t
    exact ⟨c, funext hc⟩
  have le := Fintype.card_le_of_surjective eval surj
  rw [code_count] at le
  simp [Table] at le
  exact (Nat.not_le_of_lt h) le

example (eval : Code 8 8 → Table 8) :
    ∃ t : Table 8, ∀ c : Code 8 8, ∃ x, eval c x ≠ t x :=
  missing_table 8 8 eval (by decide)

end CircuitCounting
