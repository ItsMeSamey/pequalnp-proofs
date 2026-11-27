import Q1PrivateBatch
import Q1DoubleCubeCenters

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open Private

variable {n a w r : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {C : Circuit} {A : Fin a → Clause n} {W : Fin w → Clause n}

/-- At an arbitrarily large projected pure batch, one ordinary star center
simultaneously anchors every physical slot and both endpoints of every
assigned edge. The star membership is preserved, not only adjacency. -/
theorem rich_batch_anchor (P : Batch G C A W r) (hr : 3 ≤ r) (four : NoFourCycle G) :
    ∃ v, (∀ i b, G.Adj v (P.pt i b)) ∧
      ∀ c z, z ∈ literals A W c → G.Adj v z ∧ s(v,z) ∈ starEdges G C := by
  classical
  let z : Fin r := ⟨0,by omega⟩
  let o : Fin r := ⟨1,by omega⟩
  let t : Fin r := ⟨2,by omega⟩
  have zo : z ≠ o := by intro h; have := congrArg Fin.val h; simp [z,o] at this
  have zt : z ≠ t := by intro h; have := congrArg Fin.val h; simp [z,t] at this
  have ot : o ≠ t := by intro h; have := congrArg Fin.val h; simp [o,t] at this
  have many (i : Fin r) : ∃ j k : Fin r, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
    by_cases h : i=z
    · subst i; exact ⟨o,t,zo.symm,zt.symm,ot⟩
    by_cases h' : i=o
    · subst i; exact ⟨z,t,zo,ot.symm,zt⟩
    exact ⟨z,o,(Ne.symm h),(Ne.symm h'),zo⟩
  letI : Nonempty (Fin r) := ⟨z⟩
  have hits (c) (i) : ∃ b, P.pt i b ∈ literals A W c := by
    rcases P.hits c i with h|h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  have anchored (c) : ∃ v, ∀ y ∈ literals A W c, G.Adj v y ∧ s(v,y) ∈ starEdges G C := by
    obtain ⟨b,hb⟩ := hits c z
    obtain ⟨d,hd⟩ := hits c o
    exact P.anchor c _ hb _ hd (P.sep z o zo b d)
  choose center spec using anchored
  have rejected (f : Fin r → Bool) : ∃ c, ∀ i, P.pt i (f i) ∈ literals A W c := by
    obtain ⟨c,miss⟩ := P.reject fun i => !(f i)
    refine ⟨c,fun i => ?_⟩
    have missed := miss i
    have hit := P.hits c i
    cases e : f i <;> simp_all
  obtain ⟨v,hv,owners⟩ := rich_common_center P.pt center (fun c y => y ∈ literals A W c)
    G.Adj many (fun h => P.sep _ _ h) rejected hits (fun c y h => (spec c y h).1)
    (fun ne ac ad bc bd => common_center four ne ac ad bc bd)
  exact ⟨v,hv,fun c y hy => (owners c) ▸ spec c y hy⟩

/-- If two rich roots share a physical slot then their ordinary centers agree.
Thus the entire second batch lies in the first root's neighborhood. -/
theorem rich_shared_neighborhood {a' w' h : ℕ} {A' : Fin a' → Clause n} {W' : Fin w' → Clause n}
    (P : Batch G C A' W' h) (rich : 3 ≤ h) (four : NoFourCycle G)
    (c : Fin a' ⊕ Fin w') (v : Fin n) (shared : ∀ y ∈ literals A' W' c, G.Adj v y) :
    ∀ i b, G.Adj v (P.pt i b) := by
  obtain ⟨v',neigh,anchors⟩ := rich_batch_anchor P rich four
  let k : Fin h := ⟨0,by omega⟩
  let j : Fin h := ⟨1,by omega⟩
  have kj : k ≠ j := by intro e; have := congrArg Fin.val e; simp [k,j] at this
  have hit (i) : ∃ b, P.pt i b ∈ literals A' W' c := by
    rcases P.hits c i with m|m
    · exact ⟨false,m⟩
    · exact ⟨true,m⟩
  obtain ⟨b,hb⟩ := hit k
  obtain ⟨d,hd⟩ := hit j
  have eq := common_center four (P.sep k j kj b d) (shared _ hb) (shared _ hd)
    (anchors c _ hb).1 (anchors c _ hd).1
  simpa only [eq] using neigh

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
