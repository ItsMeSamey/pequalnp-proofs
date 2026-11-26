import Research.CrownWeightedCover

namespace CrownWeightedCover
open scoped BigOperators

inductive OrTree (α : Type*)
  | leaf (i : α)
  | join (left right : OrTree α)

def OrTree.labels {α : Type*} [DecidableEq α] : OrTree α → Finset α
  | .leaf i => {i}
  | .join l r => l.labels ∪ r.labels

/-- Every leaf appears at depth at most its label's individual allowance. -/
def OrTree.depthOK {α : Type*} (limit : α → ℕ) : OrTree α → ℕ → Prop
  | .leaf i, d => d ≤ limit i
  | .join l r, d => l.depthOK limit (d+1) ∧ r.depthOK limit (d+1)

theorem tree_kraft {α : Type*} [DecidableEq α] (limit : α → ℕ) (cap : ∀ i, limit i ≤ 2)
    (T : OrTree α) (d : ℕ) (ok : T.depthOK limit d) :
    (2^d) * (∑ i ∈ T.labels, 2^(2-limit i)) ≤ 4 := by
  induction T generalizing d with
  | leaf i =>
    change d ≤ limit i at ok
    simp only [OrTree.labels,Finset.sum_singleton,←Nat.pow_add]
    exact le_trans (Nat.pow_le_pow_right (n := 2) (by decide) (by have := cap i; omega : d+(2-limit i) ≤ 2)) (by decide)
  | join l r il ir =>
    obtain ⟨hl,hr⟩ := ok
    have a := il (d+1) hl
    have b := ir (d+1) hr
    have hu : (∑ i ∈ l.labels ∪ r.labels, 2^(2-limit i)) ≤
        (∑ i ∈ l.labels, 2^(2-limit i)) + ∑ i ∈ r.labels, 2^(2-limit i) := by
      have hh := Finset.sum_union_inter (s₁ := l.labels) (s₂ := r.labels) (f := fun i => (2:ℕ)^(2-limit i))
      omega
    change 2^d * (∑ i ∈ l.labels ∪ r.labels, 2^(2-limit i)) ≤ 4
    have h := Nat.mul_le_mul_left (2^d) hu
    rw [Nat.mul_add] at h
    simp only [pow_succ',Nat.mul_assoc] at a b
    omega

theorem two_depth_crown_cover {n k : ℕ} (R C : Fin k → OrTree (Fin n))
    (dr dc : Fin n → ℕ) (budget : ∀ i, dr i + dc i ≤ 2)
    (rowDepth : ∀ t, (R t).depthOK dr 0) (colDepth : ∀ t, (C t).depthOK dc 0)
    (cover : ∀ i j : Fin n, i ≠ j → ∃ t, i ∈ (R t).labels ∧ j ∈ (C t).labels) :
    n*(n-1) ≤ 4*k := by
  apply crown_weighted_cover (fun t => (R t).labels) (fun t => (C t).labels)
    (fun i => 2^(2-dr i)) (fun i => 2^(2-dc i)) _ _ _ cover
  · intro i
    rw [←Nat.pow_add]
    exact Nat.pow_le_pow_right (n := 2) (by decide) (by have := budget i; omega : 2 ≤ (2-dr i)+(2-dc i))
  · intro t
    simpa using tree_kraft dr (fun i => by have := budget i; omega) (R t) 0 (rowDepth t)
  · intro t
    simpa using tree_kraft dc (fun i => by have := budget i; omega) (C t) 0 (colDepth t)
end CrownWeightedCover
