import Research.CircuitRewire
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
namespace IncidenceOperandLedger
open CircuitRewire
open scoped BigOperators

/-- Both original pins are counted, including tied operands. -/
def occ (g : Gate) (w : ℕ) : ℤ :=
  (if g.left = w then 1 else 0) + (if g.right = w then 1 else 0)
def fan (g : ℕ → Gate) (s w : ℕ) : ℤ := ∑ i ∈ Finset.range s, occ (g i) w
def bit (x : Bool) : ℤ := if x then 1 else 0
def zeros (z : ℕ → Bool) (g : Gate) : ℤ := bit (z g.left) + bit (z g.right)
def oneAnd (z : ℕ → Bool) (g : Gate) : ℤ :=
  if g.op = .meet ∧ z g.left ≠ z g.right then 1 else 0
def removed (z : ℕ → Bool) (g : Gate) : ℤ := bit (z g.left || z g.right)

theorem single_slots (g : Gate) (z : ℕ → Bool) (W : ℕ)
    (hl : g.left < W) (hr : g.right < W) :
    (∑ w ∈ Finset.range W, occ g w * bit (z w)) = zeros z g := by
  classical
  simp [occ, add_mul, Finset.sum_add_distrib, ite_mul, hl, hr, zeros,
    Finset.sum_ite_eq]

theorem flow (g : ℕ → Gate) (z : ℕ → Bool) (n s : ℕ)
    (valid : ∀ i < s, (g i).left < n+s ∧ (g i).right < n+s) :
    (∑ i ∈ Finset.range s, zeros z (g i)) =
    (∑ w ∈ Finset.range n, fan g s w * bit (z w)) +
    ∑ i ∈ Finset.range s, fan g s (n+i) * bit (z (n+i)) := by
  classical
  rw [← Finset.sum_range_add]
  simp only [fan, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact (single_slots (g i) z _ (valid i (Finset.mem_range.mp hi)).1
    (valid i (Finset.mem_range.mp hi)).2).symm

def zeroAt (z : ℕ → Bool) (g : Gate) : Bool :=
  match g.op with
  | .join => z g.left && z g.right
  | .meet => z g.left || z g.right
  | .copy => z g.left
  | .zero => true

theorem slot_identity (z : ℕ → Bool) (g : Gate)
    (binary : g.op = .join ∨ g.op = .meet) :
    removed z g = zeros z g - bit (zeroAt z g) + oneAnd z g := by
  rcases binary with h|h <;> cases a : z g.left <;> cases b : z g.right <;>
    simp [removed, zeros, zeroAt, oneAnd, bit, h, a, b]

theorem literal_ledger (g : ℕ → Gate) (z : ℕ → Bool) (n s : ℕ)
    (valid : ∀ i < s, (g i).left < n+s ∧ (g i).right < n+s)
    (binary : ∀ i < s, (g i).op = .join ∨ (g i).op = .meet)
    (eval : ∀ i < s, z (n+i) = zeroAt z (g i)) :
    (∑ i ∈ Finset.range s, removed z (g i)) =
    (∑ w ∈ Finset.range n, fan g s w * bit (z w)) +
    (∑ i ∈ Finset.range s, (fan g s (n+i)-1) * bit (z (n+i))) +
    ∑ i ∈ Finset.range s, oneAnd z (g i) := by
  classical
  calc
    _ = ∑ i ∈ Finset.range s, (zeros z (g i) - bit (z (n+i)) + oneAnd z (g i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [eval i (Finset.mem_range.mp hi)]
      exact slot_identity z _ (binary i (Finset.mem_range.mp hi))
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_mul, one_mul]
      rw [flow g z n s valid]
      ring
#print axioms literal_ledger
end IncidenceOperandLedger
