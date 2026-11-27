import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4186_aux.Q0Transversal

/-- A clause hitting each edge excludes at most one choice of endpoints.
    The hypotheses say each transversal misses some clause and each clause
    contains one or both endpoints of each edge. -/
theorem pow_le_card {V K : Type*} [Fintype K] {r : ℕ}
    (endpoint : Fin r → Bool → V) (contains : K → V → Prop)
    (hits : ∀ c i, contains c (endpoint i false) ∨ contains c (endpoint i true))
    (misses : ∀ t : Fin r → Bool, ∃ c, ∀ i, ¬ contains c (endpoint i (t i))) :
    2 ^ r ≤ Fintype.card K := by
  classical
  choose select absent using misses
  have injective : Function.Injective select := by
    intro t u eq
    funext i
    have ht := absent t i
    have hu := absent u i
    rw [← eq] at hu
    have hit := hits (select t) i
    cases et : t i <;> cases eu : u i <;> simp_all
  simpa using Fintype.card_le_of_injective select injective

theorem twice_le_pow (r : ℕ) : 2 * r ≤ 2 ^ r := by
  cases r with
  | zero => decide
  | succ r =>
    induction r with
    | zero => decide
    | succ r ih =>
      rw [pow_succ]
      omega

/-- Convenient form for a top having at most d+2 primitive clauses. -/
theorem local_charge {V K : Type*} [Fintype K] {r d : ℕ}
    (endpoint : Fin r → Bool → V) (contains : K → V → Prop)
    (hits : ∀ c i, contains c (endpoint i false) ∨ contains c (endpoint i true))
    (misses : ∀ t : Fin r → Bool, ∃ c, ∀ i, ¬ contains c (endpoint i (t i)))
    (clauseBound : Fintype.card K ≤ d + 2) : 2 * r ≤ d + 2 :=
  (twice_le_pow r).trans ((pow_le_card endpoint contains hits misses).trans clauseBound)

end PEqualNP.Outside.L_meta_4186_aux.Q0Transversal
