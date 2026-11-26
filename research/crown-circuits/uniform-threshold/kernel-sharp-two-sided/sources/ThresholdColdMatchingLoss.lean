import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite counting on supplied sets. No circuit or physical receiver assertion. -/
namespace ThresholdColdMatchingLoss

variable {P X V : Type*} [DecidableEq P] [DecidableEq X]

/-- In a matching application a candidate is an unordered pair of disjoint rows;
its box is their four-element vertex union. Each candidate has exactly one box. -/
def fiber (pool : Finset P) (box : P → X) (x : X) : Finset P :=
  pool.filter (fun p => box p=x)

def loss (boxes : Finset X) (pool : Finset P) (box : P → X) : ℕ :=
  ∑ x ∈ boxes, ((fiber pool box x).card - 1)

/-- On a box containing two or more candidates, at most one candidate may
avoid both exceptional sets. Singleton boxes incur exactly zero loss. -/
theorem loss_le_exceptions (boxes : Finset X) (pool missing cold : Finset P)
    (box : P → X)
    (hot_unique : ∀ x ∈ boxes, 2 ≤ (fiber pool box x).card →
      ((fiber pool box x) \ (missing ∪ cold)).card ≤ 1) :
    loss boxes pool box ≤ missing.card + cold.card := by
  let bad := missing ∪ cold
  have point (x : X) (mem : x∈boxes) :
      (fiber pool box x).card - 1 ≤ (fiber bad box x).card := by
    by_cases large : 2 ≤ (fiber pool box x).card
    · have cover : fiber pool box x ⊆ fiber bad box x ∪ (fiber pool box x \ bad) := by
        intro p hp
        by_cases h : p∈bad
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h,(Finset.mem_filter.mp hp).2⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp,h⟩)
      have bound := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
      have one : (fiber pool box x \ bad).card ≤ 1 := hot_unique x mem large
      omega
    · omega
  calc
    loss boxes pool box ≤ ∑ x ∈ boxes, (fiber bad box x).card := Finset.sum_le_sum point
    _ = (bad.filter (fun p => box p ∈ boxes)).card := Finset.sum_card_fiberwise_eq_card_filter bad boxes box
    _ ≤ bad.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ missing.card+cold.card := Finset.card_union_le _ _

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Keys are (opposite row edge B, surviving original endpoint S). An endpoint
v of B must be adjacent to S. The same key may have two such witnesses. -/
def keys : Finset (Sym2 V × V) :=
  Finset.univ.biUnion (fun v : V => (G.incidenceFinset v).product (G.neighborFinset v))

theorem keys_card :
    (keys G).card ≤ ∑ v : V, G.degree v ^ 2 := by
  calc
    (keys G).card ≤ ∑ v : V, ((G.incidenceFinset v).product (G.neighborFinset v)).card :=
      Finset.card_biUnion_le
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      change ((G.incidenceFinset v) ×ˢ (G.neighborFinset v)).card = G.degree v ^ 2
      rw [Finset.card_product,SimpleGraph.card_incidenceFinset_eq_degree,
        SimpleGraph.card_neighborFinset_eq_degree,pow_two]

/-- Physical proofs must provide reach and the multiplicity per (B,S).
The two candidate rows need not have a fixed orientation across the family. -/
theorem cold_le_degree_squares (cold : Finset P) (opposite : P → Sym2 V)
    (original : P → V)
    (reach : ∀ p ∈ cold, ∃ v, opposite p ∈ G.incidenceFinset v ∧ G.Adj v (original p))
    (multiplicity : ∀ B S, (cold.filter (fun p => (opposite p,original p)=(B,S))).card ≤ 2) :
    cold.card ≤ 2 * ∑ v : V, G.degree v ^ 2 := by
  let key := fun p => (opposite p,original p)
  have inside (p : P) (hp : p∈cold) : key p ∈ keys G := by
    obtain ⟨v,hv,hn⟩ := reach p hp
    exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ v,
      Finset.mem_product.mpr ⟨hv,(G.mem_neighborFinset v (original p)).mpr hn⟩⟩
  have unchanged : cold.filter (fun p => key p∈keys G) = cold :=
    Finset.filter_eq_self.mpr inside
  calc
    cold.card = ∑ k ∈ keys G, (cold.filter (fun p => key p=k)).card := by
      rw [Finset.sum_card_fiberwise_eq_card_filter,unchanged]
    _ ≤ ∑ _k ∈ keys G, 2 := Finset.sum_le_sum (fun k _ => multiplicity k.1 k.2)
    _ = 2*(keys G).card := by simp [Nat.mul_comm]
    _ ≤ 2 * ∑ v : V, G.degree v ^ 2 := Nat.mul_le_mul_left _ (keys_card G)

theorem loss_le_missing_add_degree_squares
    (boxes : Finset X) (pool missing cold : Finset P) (box : P → X)
    (opposite : P → Sym2 V) (original : P → V)
    (hot_unique : ∀ x ∈ boxes, 2 ≤ (fiber pool box x).card →
      ((fiber pool box x) \ (missing ∪ cold)).card ≤ 1)
    (reach : ∀ p ∈ cold, ∃ v, opposite p ∈ G.incidenceFinset v ∧ G.Adj v (original p))
    (multiplicity : ∀ B S, (cold.filter (fun p => (opposite p,original p)=(B,S))).card ≤ 2) :
    loss boxes pool box ≤ missing.card + 2 * ∑ v : V, G.degree v ^ 2 :=
  (loss_le_exceptions boxes pool missing cold box hot_unique).trans
    (Nat.add_le_add_left (cold_le_degree_squares G cold opposite original reach multiplicity) _)

end ThresholdColdMatchingLoss
