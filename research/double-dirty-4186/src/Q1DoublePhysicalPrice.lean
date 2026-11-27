import Q1DoublePrices

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open scoped BigOperators

/-- Count raw occurrences of a concrete double-dirty component in the original
circuit. The two arm regions include their dirty output gates. The guard and each
external region include their clean top, which is removed from the dirty charge. -/
theorem physical_mixer_price (n : ℕ) (C : Circuit)
    (I armA armB guard pool tops : Finset ℕ) (ext : ℕ → Finset ℕ)
    (a b H : ℕ) (top : ℕ → ℕ) (mPin : ℕ × Fin 2)
    (cuts : ℕ → Finset (ℕ × Fin 2))
    (rootA : a ∈ armA) (rootB : b ∈ armB) (rootW : H ∈ guard)
    (rootE : ∀ i ∈ I, top i ∈ ext i)
    (useA : ∀ j ∈ armA.erase a, ∃ p ∈ pins armA, opnd C p.1 p.2 = n+j)
    (useB : ∀ j ∈ armB.erase b, ∃ p ∈ pins armB, opnd C p.1 p.2 = n+j)
    (useW : ∀ j ∈ guard.erase H, ∃ p ∈ pins guard, opnd C p.1 p.2 = n+j)
    (useE : ∀ i ∈ I, ∀ j ∈ (ext i).erase (top i),
      ∃ p ∈ pins (ext i), opnd C p.1 p.2 = n+j)
    (mCut : mPin ∈ occurrences n C guard)
    (eCut : ∀ i ∈ I, cuts i ⊆ occurrences n C (ext i))
    (privDisj : (I : Set ℕ).PairwiseDisjoint (fun i => (ext i).erase (top i)))
    (ab : Disjoint armA armB) (gw : Disjoint (armA ∪ armB) (guard.erase H))
    (ex : Disjoint (armA ∪ armB ∪ guard.erase H) (I.biUnion fun i => (ext i).erase (top i)))
    (inside : armA ∪ armB ∪ guard.erase H ∪ (I.biUnion fun i => (ext i).erase (top i)) ⊆ pool)
    (central : H ∈ tops) (fresh : ∀ i ∈ I, top i ≠ H)
    (realTop : ∀ i ∈ I, top i ∈ tops) (distinct : Set.InjOn top (I : Set ℕ)) :
    (occurrences n C armA).card + (occurrences n C armB).card +
        ((occurrences n C guard).erase mPin).card +
      (∑ i ∈ I, (((occurrences n C (ext i)) \ cuts i).card + (cuts i).card)) ≤
      pool.card + 2 * tops.card + 1 := by
  have sizeTop : I.card + 1 ≤ tops.card := by
    have inj : (I.image top).card = I.card := Finset.card_image_of_injOn distinct
    have miss : H ∉ I.image top := fun h => by
      obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      exact fresh i hi eq
    have insideTop : insert H (I.image top) ⊆ tops := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact central
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
        exact realTop i hi
    simpa [Finset.card_insert_of_notMem miss, inj] using Finset.card_le_card insideTop
  apply mixer_allowance I _ _ _ armA.card armB.card (guard.erase H).card
    _ _ (fun i => ((ext i).erase (top i)).card) pool.card tops.card
  · exact occurrence_bound n C armA a rootA useA
  · exact occurrence_bound n C armB b rootB useB
  · exact guard_occurrences n C guard H rootW useW mPin mCut
  · intro i hi
    exact external_slots n C (ext i) (top i) (rootE i hi) (useE i hi) (cuts i) (eCut i hi)
  · exact physical_region_bound I armA armB (guard.erase H) pool _ privDisj ab gw ex inside
  · exact sizeTop

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
