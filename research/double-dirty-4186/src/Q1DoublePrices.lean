import Q1DoubleLedger

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open scoped BigOperators

/-- Cut shared subtrees at their actual operand occurrences. The exposed external root
pays once for each cut pin, and once for each remaining primitive occurrence. -/
theorem external_slots (n : ℕ) (C : Circuit) (js : Finset ℕ) (root : ℕ) (hr : root ∈ js)
    (used : ∀ j ∈ js.erase root, ∃ p ∈ pins js, opnd C p.1 p.2 = n+j)
    (cuts : Finset (ℕ × Fin 2)) (hc : cuts ⊆ occurrences n C js) :
    ((occurrences n C js) \ cuts).card + cuts.card ≤ (js.erase root).card + 2 := by
  rw [Finset.card_sdiff_add_card_eq_card hc]
  have h := occurrence_bound n C js root hr used
  have hh := Finset.card_erase_add_one hr
  omega

/-- Original resource bound when a central component has two arms, one guard, and
arbitrarily many external roots. An external root pays one slot for each cut subtree
and one for each private occurrence. The shared guard appears only on the left once. -/
theorem mixer_allowance (I : Finset ℕ) (a b w : ℕ)
    (dA dB dW : ℕ) (z cuts dE : ℕ → ℕ) (D roots : ℕ)
    (ha : a ≤ dA + 1) (hb : b ≤ dB + 1) (hw : w ≤ dW + 1)
    (external : ∀ i ∈ I, z i + cuts i ≤ dE i + 2)
    (gates : dA + dB + dW + (∑ i ∈ I, dE i) ≤ D)
    (count : I.card + 1 ≤ roots) :
    a + b + w + (∑ i ∈ I, (z i + cuts i)) ≤ D + 2 * roots + 1 := by
  have hsum := Finset.sum_le_sum external
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at hsum
  simp only [Finset.sum_add_distrib]
  omega

/-- Four disjoint physical charges: the two arms, the residual guard gates (which
exclude the centreless top), and the disjoint external-private regions. -/
theorem physical_region_bound (I armA armB guard pool : Finset ℕ) (external : ℕ → Finset ℕ)
    (privDisj : (I : Set ℕ).PairwiseDisjoint external) (ab : Disjoint armA armB)
    (gw : Disjoint (armA ∪ armB) guard)
    (ex : Disjoint (armA ∪ armB ∪ guard) (I.biUnion external))
    (inside : armA ∪ armB ∪ guard ∪ I.biUnion external ⊆ pool) :
    armA.card + armB.card + guard.card + (∑ i ∈ I, (external i).card) ≤ pool.card := by
  have h := Finset.card_le_card inside
  rwa [Finset.card_union_of_disjoint ex, Finset.card_union_of_disjoint gw,
    Finset.card_union_of_disjoint ab, Finset.card_biUnion privDisj] at h

/-- No external leak: both arms and one shared guard. -/
theorem no_leak_price (a b w : ℕ) : a+b+w+(∑ _i ∈ (∅ : Finset ℕ), 0) = a+b+w := by simp

/-- One shared subtree with k leaves appears in the arm. The external root pays
only for its private leaves and the single input referencing that subtree. -/
theorem one_leak_price (i k x z b w : ℕ) :
    (k+x)+b+w+(∑ _j ∈ ({i} : Finset ℕ), (z+1)) = k+x+z+b+w+1 := by simp; omega

/-- All shared subtrees are on one arm, and every external root has one input cut. -/
theorem many_leak_price (I : Finset ℕ) (a b w : ℕ) (z : ℕ → ℕ) :
    a+b+w+(∑ i ∈ I, (z i+1)) = a+b+w+(∑ i ∈ I, z i)+I.card := by
  simp [Finset.sum_add_distrib, Nat.add_assoc]

/-- In the two-sided case the two shared subtrees terminate at the same external
root. Its two cut inputs both count even if its private batch has no edges. -/
theorem triangle_price (e x y w i j k : ℕ) :
    (x+i)+(y+j)+w+(∑ _t ∈ ({e} : Finset ℕ), (k+2)) = x+y+w+i+j+k+2 := by simp; omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
