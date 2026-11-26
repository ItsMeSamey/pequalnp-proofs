import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
The numerical implication for the proposed threshold-two lower bound.
All counts in the regular case are integers, including the possibly negative
excess over two gates per input. The circuit-theoretic dichotomy is a hypothesis.
-/
namespace ThresholdFourThirds

structure Regular (n s : ℤ) where
  a : ℤ
  v : ℤ
  c : ℤ
  D : ℤ
  and_nonneg : 0 ≤ a
  degree_nonneg : 0 ≤ D
  vertices : v ≤ 2 * a + s + 2
  ands : a ≤ s + 4
  degree : D ≤ s - a + 4 + c
  edges : 2 * n ≤ 2 * c + (v - 2 * c) * (D + 2)
  components : 2 * c ≤ v

/-- The sign is deliberately retained for induction and square-root extraction. -/
def Bound (n s : ℤ) : Prop :=
  1 ≤ s + 6 ∧ 16 * (n + 3) ≤ 9 * (s + 6) ^ 2

theorem regular_bound {n s : ℤ} (h : Regular n s) : Bound n s := by
  let A := 2 * h.a + s + 2 - 2 * h.c
  let B := s - h.a + 4 + h.c + 2
  have ha : h.v - 2 * h.c ≤ A := by dsimp [A]; linarith [h.vertices]
  have hb : h.D + 2 ≤ B := by dsimp [B]; linarith [h.degree]
  have hzero : 0 ≤ A := by linarith [h.components, ha]
  have hmul : (h.v - 2 * h.c) * (h.D + 2) ≤ A * B :=
    (mul_le_mul_of_nonneg_right ha (by linarith [h.degree_nonneg])).trans
      (mul_le_mul_of_nonneg_left hb hzero)
  have havg : 8 * (A * B) ≤ (3 * s + 14) ^ 2 := by
    dsimp [A, B]
    nlinarith [sq_nonneg ((2 * h.a + s + 2 - 2 * h.c) -
      2 * (s - h.a + 4 + h.c + 2))]
  have hcomp : 2 * h.c ≤ 3 * s + 10 := by
    linarith [h.components, h.vertices, h.ands]
  constructor
  · linarith [h.ands, h.and_nonneg]
  · nlinarith [h.edges, hmul, havg, hcomp]

theorem base_bound {g : ℤ} (hg : 1 ≤ g) : Bound 2 (g - 4) := by
  constructor
  · omega
  · nlinarith [mul_nonneg (show 0 ≤ g - 1 by omega) (show 0 ≤ g + 5 by omega)]

theorem deletion_step {n s s' : ℤ} (h : Bound n s) (hs : s + 1 ≤ s') :
    Bound (n + 1) s' := by
  obtain ⟨hp, hsq⟩ := h
  have hmul : 0 ≤ (s' - s - 1) * (s' + s + 13) :=
    mul_nonneg (by omega) (by omega)
  constructor
  · omega
  · nlinarith

def excess (C : ℕ → ℤ) (n : ℕ) : ℤ := C n - 2 * (n : ℤ)

/-- Starting at two inputs, either deletion or the regular ledger suffices. -/
theorem uniform_squared (C : ℕ → ℤ) (base : 1 ≤ C 2)
    (step : ∀ n : ℕ, 2 ≤ n →
      C n + 3 ≤ C (n + 1) ∨ Nonempty (Regular ((n + 1 : ℕ) : ℤ) (excess C (n + 1))))
    {n : ℕ} (hn : 2 ≤ n) : Bound (n : ℤ) (excess C n) := by
  have aux : ∀ k : ℕ, Bound ((k + 2 : ℕ) : ℤ) (excess C (k + 2)) := by
    intro k
    induction k with
    | zero =>
      simpa [excess] using base_bound base
    | succ k ih =>
      rcases step (k + 2) (by omega) with hd | hr
      · have hs : excess C (k + 2) + 1 ≤ excess C ((k + 2) + 1) := by
          unfold excess
          push_cast
          omega
        have hh := deletion_step ih hs
        change Bound (((k + 2) + 1 : ℕ) : ℤ) (excess C ((k + 2) + 1))
        rw [Nat.cast_add, Nat.cast_one]
        exact hh
      · exact hr.elim (fun ledger => regular_bound ledger)
  have heq : n - 2 + 2 = n := by omega
  simpa only [heq] using aux (n - 2)

end ThresholdFourThirds
