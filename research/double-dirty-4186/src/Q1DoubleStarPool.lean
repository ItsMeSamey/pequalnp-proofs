import Q1DoubleStarCubes
import Q1PrivateBatch

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm Private
open scoped BigOperators

/-- A physical slot class can be shared by any number of pooled roots.
The maps from local pins to physical labels may identify repeated pins.
Disjoint assignment of actual edges, membership of the endpoints in one
neighborhood, and the projected batches' ordinary cleanliness suffice. -/
theorem weighted_batch_pool {R L : Type*} [Fintype R] [Fintype L]
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (four : NoFourCycle G) (a w r : R → ℕ)
    (A : ∀ i, Fin (a i) → Clause n) (W : ∀ i, Fin (w i) → Clause n)
    (P : ∀ i, Batch G C (A i) (W i) (r i)) (positive : ∀ i, 0 < r i)
    (id : ∀ i, (Fin (a i) ⊕ Fin (w i)) → L) (support : L → Clause n)
    (physical : ∀ i c, support (id i c) = literals (A i) (W i) c)
    (v : Fin n) (inside : ∀ i j b, G.Adj v ((P i).pt j b))
    (exclusive : ∀ i j, i ≠ j → ∀ k l b c,
      s((P i).pt k b,(P i).pt k (!b)) ≠ s((P j).pt l c,(P j).pt l (!c))) :
    (∑ i, 2^(r i)) ≤ Fintype.card L := by
  classical
  let owners (l : L) := Finset.univ.filter fun i => ∃ c, id i c = l
  apply pooled_physical_slots G r positive (fun i => (P i).pt) owners (fun l x => x ∈ support l)
  · intro l i hi j
    obtain ⟨c,rfl⟩ := (Finset.mem_filter.mp hi).2
    rw [physical]
    exact (P i).hits c j
  · intro i S h
    let T := Finset.univ.filter S
    obtain ⟨x,hx,y,hy,hxy⟩ := (P i).clean T (by
      intro c
      have mem : i ∈ owners (id i c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,c,rfl⟩
      obtain ⟨x,hs,hx⟩ := h (id i c) mem
      exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩,physical i c ▸ hx⟩)
    exact ⟨x,y,(Finset.mem_filter.mp hx).2,(Finset.mem_filter.mp hy).2,hxy⟩
  · intro t i k j l adj
    by_cases ij : i=j
    · subst j
      by_cases eq : k=l
      · subst l; exact G.irrefl adj
      · exact (P i).induced k l eq _ _ adj
    · let b := t i k
      let c := t j l
      have left := nbhd_matching four (inside i k b) (inside j l c) (inside i k (!b))
        adj ((P i).edges k b)
      have right := nbhd_matching four (inside j l c) (inside i k b) (inside j l (!c))
        adj.symm ((P j).edges l c)
      apply exclusive i j ij k l b c
      change s((P i).pt k b,(P i).pt k (!b)) = s((P j).pt l c,(P j).pt l (!c))
      rw [← left,← right]
      exact Sym2.eq_swap
end PEqualNP.Outside.L_meta_4186_aux.Q1Double
