import Q1DoubleStarCharge

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open scoped BigOperators

/-- The two alternatives for a rich central root. A deficient external
double forces exponentially many shared slots. Otherwise all crossing and
empty batches can be paid privately and all positive internal batches are
pooled in the central neighborhood. -/
def RichStarLedger {I : Type*} [Fintype I] (k p h : I → ℕ) (r s a b w : ℕ) : Prop :=
  (∃ i, h i=2 ∧ p i=2 ∧ 2^r ≤ k i) ∨
  ∃ internal : Finset I, (∀ i ∉ internal, 2*h i ≤ p i+1) ∧
    (if s≤2 then 2^r + ∑ i ∈ internal, 2^(h i) ≤ a+w+∑ i ∈ internal, p i
     else 2^r+2^s + ∑ i ∈ internal, 2^(h i) ≤ a+b+w+∑ i ∈ internal, p i)

/-- The one-arm endpoint budget for arbitrary external multiplicities and
batch sizes. The low case has a single tight-slot test; the high case uses
the physically pooled estimate or the deficient crossing witness. -/
theorem one_arm_multi_leak {I : Type*} [Fintype I] (k p h : I → ℕ)
    (r s x b w : ℕ) (leaks : 2 ≤ Fintype.card I) (hb : 2 ≤ b)
    (hk : ∀ i, 2 ≤ k i) (hp : ∀ i, 1 ≤ p i) (ext : ∀ i, 2^(h i) ≤ k i+p i)
    (tight : ∀ i, h i=2 → k i+p i=4 → r≤1) (partner : 2*s ≤ b+w)
    (high : 3≤r → RichStarLedger k p h r s (x+∑ i, k i) b w) :
    2*r+2*s+∑ i, 2*h i ≤ x+b+w+∑ i, (k i+p i+1) := by
  classical
  by_cases small : r ≤ Fintype.card I
  · exact low_star_charge k p h r s x b w leaks small hk hp ext tight partner
  have rich : 3 ≤ r := by omega
  rcases high rich with ⟨i,he,hp',deficit⟩|⟨internal,paid,pool⟩
  · exact rich_deficient_charge k p h r s x b w rich i he hp' deficit
      (fun j => (Q0Transversal.twice_le_pow _).trans (ext j)) partner
  · have move : (x+∑ i, k i)+b+w+∑ i, (p i+1) = x+b+w+∑ i, (k i+p i+1) := by
      simp only [Finset.sum_add_distrib]
      omega
    rw [← move]
    by_cases little : s≤2
    · exact rich_pool_small_opposite h p internal r s _ b w rich little hb
        (by simpa only [if_pos little] using pool) paid
    · exact rich_pool_large_opposite h p internal r s _ b w
        (by simpa only [if_neg little] using pool) paid

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
