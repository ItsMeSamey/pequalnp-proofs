import Q1CoverUnion

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm
open scoped BigOperators

/-- Both positions remain distinct, even when two leaves denote the same support. -/
def pins (js : Finset ℕ) := js ×ˢ (Finset.univ : Finset (Fin 2))

def internal (n : ℕ) (C : Circuit) (js : Finset ℕ) :=
  (pins js).filter fun p => ∃ j ∈ js, opnd C p.1 p.2 = n+j

def occurrences (n : ℕ) (C : Circuit) (js : Finset ℕ) :=
  pins js \ internal n C js

/-- Each non-root gate is used by at least one internal pin. This controls leaves even
if internal sharing occurs. Neither supports nor input wire numbers are deduplicated. -/
theorem occurrence_bound (n : ℕ) (C : Circuit) (js : Finset ℕ) (root : ℕ)
    (hr : root ∈ js) (used : ∀ j ∈ js.erase root, ∃ p ∈ pins js, opnd C p.1 p.2 = n+j) :
    (occurrences n C js).card ≤ js.card + 1 := by
  classical
  have incl : js.erase root ⊆ (internal n C js).image (fun p => opnd C p.1 p.2 - n) := by
    intro j hj
    obtain ⟨p,hp,eq⟩ := used j hj
    apply Finset.mem_image.mpr
    exact ⟨p, Finset.mem_filter.mpr ⟨hp,j,Finset.mem_of_mem_erase hj,eq⟩, by rw [eq]; omega⟩
  have hi := (Finset.card_le_card incl).trans Finset.card_image_le
  have hsub : internal n C js ⊆ pins js := Finset.filter_subset _ _
  have total := Finset.card_sdiff_add_card_eq_card hsub
  have hpins : (pins js).card = js.card * 2 := by simp [pins, Finset.card_product]
  have hroot := Finset.card_erase_add_one hr
  unfold occurrences
  omega

/-- The common guard omits the mixer input occurrence. For a one-clause guard this
leaves one ordinary pin and requires no dirty guard gate. -/
theorem guard_occurrences (n : ℕ) (C : Circuit) (js : Finset ℕ) (top : ℕ)
    (ht : top ∈ js) (used : ∀ j ∈ js.erase top, ∃ p ∈ pins js, opnd C p.1 p.2 = n+j)
    (mixerPin : ℕ × Fin 2) (hm : mixerPin ∈ occurrences n C js) :
    ((occurrences n C js).erase mixerPin).card ≤ (js.erase top).card + 1 := by
  have hb := occurrence_bound n C js top ht used
  have h1 := Finset.card_erase_add_one hm
  have h2 := Finset.card_erase_add_one ht
  omega

private theorem minimum_cover {n : ℕ} (H : SimpleGraph (Fin n)) :
    ∃ K : Finset (Fin n), IsMinCover H K := by
  classical
  let P := fun k : ℕ => ∃ K : Finset (Fin n), H.IsVertexCover (K : Set (Fin n)) ∧ K.card = k
  have ex : ∃ k, P k := ⟨_, Finset.univ, by simp, rfl⟩
  obtain ⟨K, hc, hk⟩ := Nat.find_spec ex
  refine ⟨K,hc,?_⟩
  intro T hT
  rw [hk]
  exact Nat.find_min' ex (show P T.card from ⟨T,hT,rfl⟩)

theorem disjoint_charge {ι α : Type*} [DecidableEq α] (I : Finset ι)
    (region : ι → Finset α) (pool : Finset α)
    (sub : ∀ i ∈ I, region i ⊆ pool)
    (disj : (I : Set ι).PairwiseDisjoint region) :
    (∑ i ∈ I, (region i).card) ≤ pool.card := by
  rw [← Finset.card_biUnion disj]
  exact Finset.card_le_card (fun _ h => by
    obtain ⟨i,hi,hm⟩ := Finset.mem_biUnion.mp h
    exact sub i hi hm)

theorem component_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (I : Finset ℕ) (pivot : ℕ)
    (dirty roots : ℕ → Finset ℕ) (edges : ℕ → Finset (Sym2 (Fin n)))
    (dirtySub : ∀ i ∈ I, dirty i ⊆ junk G C) (rootSub : ∀ i ∈ I, roots i ⊆ centreless G C)
    (dirtyDisj : (I : Set ℕ).PairwiseDisjoint dirty) (rootDisj : (I : Set ℕ).PairwiseDisjoint roots)
    (residual : Ustar G C ⊆ I.biUnion edges)
    (localCover : ∀ i ∈ I, ∃ V : Finset (Fin n),
      (∀ u v, s(u,v) ∈ edges i → u ∈ V ∨ v ∈ V) ∧ V.card + (edges i).card ≤
        (dirty i).card + 2 * (roots i).card + (if i = pivot then 1 else 0)) :
    ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card + (Ustar G C).card ≤
      (tops G C \ centreless G C).card + 2 * (centreless G C).card + (junk G C).card + 1 := by
  classical
  let U := Ustar G C
  have pick (i : ℕ) : ∃ V : Finset (Fin n), i ∈ I →
      (∀ u v, s(u,v) ∈ edges i → u ∈ V ∨ v ∈ V) ∧ V.card + (edges i).card ≤
        (dirty i).card + 2 * (roots i).card + (if i = pivot then 1 else 0) := by
    by_cases hi : i ∈ I
    · obtain ⟨V,h⟩ := localCover i hi
      exact ⟨V, fun _ => h⟩
    · exact ⟨∅, fun h => (hi h).elim⟩
  choose V hV using pick
  let W := I.biUnion V
  obtain ⟨K,hK⟩ := minimum_cover (G.deleteEdges (↑U : Set (Sym2 (Fin n))))
  have hk := (S4183.main n G C four edge least form).2 K hK
  refine ⟨K ∪ W, ?_, ?_⟩
  · intro u v adj
    by_cases he : s(u,v) ∈ U
    · obtain ⟨i,hi,hin⟩ := Finset.mem_biUnion.mp (residual he)
      rcases (hV i hi).1 u v hin with h | h
      · exact Or.inl (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hi,h⟩))
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hi,h⟩))
    · have hd : (G.deleteEdges (↑U : Set (Sym2 (Fin n)))).Adj u v :=
        SimpleGraph.deleteEdges_adj.mpr ⟨adj,he⟩
      rcases hK.1 hd with h | h
      · exact Or.inl (Finset.mem_union_left _ h)
      · exact Or.inr (Finset.mem_union_left _ h)
  · have hw : W.card ≤ ∑ i ∈ I, (V i).card := Finset.card_biUnion_le
    have hu : U.card ≤ ∑ i ∈ I, (edges i).card := (Finset.card_le_card residual).trans Finset.card_biUnion_le
    have hsum := Finset.sum_le_sum (fun i hi => (hV i hi).2)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have bonus : (∑ i ∈ I, if i = pivot then 1 else 0 : ℕ) ≤ 1 := by
      by_cases h : pivot ∈ I <;> simp [h]
    have hd := disjoint_charge I dirty _ dirtySub dirtyDisj
    have hr := disjoint_charge I roots _ rootSub rootDisj
    have hUnion := Finset.card_union_le K W
    change (K ∪ W).card + U.card ≤ _
    omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
