import Q1DoubleIntegration
import Q1DoubleIncremental

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux

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

namespace Allocation

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def allowance (A : Allocation G C) (i : ℕ) := (A.dirty i).card + 2*(A.roots i).card

theorem outsideBase (A : Allocation G C) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (paid : ∀ i ∈ A.components.erase A.pivot, A.Local i) :
    ∃ T : Finset (Fin n),
      (∀ x y, G.Adj x y → s(x,y) ∉ A.edges A.pivot → x ∈ T ∨ y ∈ T) ∧
      T.card + (Ustar G C \ A.edges A.pivot).card ≤ (tops G C \ centreless G C).card +
        ∑ i ∈ A.components.erase A.pivot, A.allowance i := by
  classical
  let I := A.components.erase A.pivot
  have get (i : ℕ) : ∃ V : Finset (Fin n), i ∈ I →
      (∀ x y, s(x,y) ∈ A.edges i → x ∈ V ∨ y ∈ V) ∧
      V.card + (A.edges i).card ≤ A.allowance i := by
    by_cases hi : i ∈ I
    · obtain ⟨V,hV,sz⟩ := paid i hi
      refine ⟨V,fun _ => ⟨hV,?_⟩⟩
      simpa [allowance,(Finset.mem_erase.mp hi).1] using sz
    · exact ⟨∅,fun h => (hi h).elim⟩
  choose V hV using get
  obtain ⟨K, minimum⟩ := minimum_cover (G.deleteEdges (↑(Ustar G C) : Set (Sym2 (Fin n))))
  have costK := (S4183.main n G C four edge least form).2 K minimum
  let W := I.biUnion V
  have sub : Ustar G C \ A.edges A.pivot ⊆ I.biUnion A.edges := by
    intro e he
    obtain ⟨res,other⟩ := Finset.mem_sdiff.mp he
    obtain ⟨i,hi,mem⟩ := Finset.mem_biUnion.mp (A.covers res)
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_erase.mpr ⟨fun h => other (h ▸ mem),hi⟩,mem⟩
  refine ⟨K ∪ W, ?_, ?_⟩
  · intro x y adj outside
    by_cases res : s(x,y) ∈ Ustar G C
    · obtain ⟨i,hi,mem⟩ := Finset.mem_biUnion.mp (sub (Finset.mem_sdiff.mpr ⟨res,outside⟩))
      rcases (hV i hi).1 x y mem with hx | hy
      · exact Or.inl (Finset.mem_union_right K (Finset.mem_biUnion.mpr ⟨i,hi,hx⟩))
      · exact Or.inr (Finset.mem_union_right K (Finset.mem_biUnion.mpr ⟨i,hi,hy⟩))
    · have h := minimum.1 (show (G.deleteEdges (↑(Ustar G C) : Set (Sym2 (Fin n)))).Adj x y from
          SimpleGraph.deleteEdges_adj.mpr ⟨adj,res⟩)
      exact h.imp (Finset.mem_union_left W) (Finset.mem_union_left W)
  · have hw : W.card ≤ ∑ i ∈ I, (V i).card := Finset.card_biUnion_le
    have hu := (Finset.card_le_card sub).trans Finset.card_biUnion_le
    have bound := Finset.sum_le_sum (s := I) (fun i hi => (hV i hi).2)
    rw [Finset.sum_add_distrib] at bound
    have union := Finset.card_union_le K W
    change (K ∪ W).card + _ ≤ _ + ∑ i ∈ I, A.allowance i
    omega

/-- One interface for all four incidence cases. The pivot proof can use the paid
ordinary and nonpivot vertices; it need only bound additional vertices. -/
theorem finishIncremental (A : Allocation G C) (four : NoFourCycle G)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (one : (orN G C \ lam G C).card = 1) (hp : A.pivot ∈ A.components)
    (paid : ∀ i ∈ A.components.erase A.pivot, A.Local i) (res : A.edges A.pivot ⊆ Ustar G C)
    (pivot : ∀ T : Finset (Fin n),
      (∀ x y, G.Adj x y → s(x,y) ∉ A.edges A.pivot → x ∈ T ∨ y ∈ T) →
      ∃ S : Finset (Fin n), (∀ a b, s(a,b) ∈ A.edges A.pivot → a ∈ T ∪ S ∨ b ∈ T ∪ S) ∧
      (T ∪ S).card + (A.edges A.pivot).card ≤ T.card + (A.allowance A.pivot + 1)) :
    Positive G C := by
  obtain ⟨T, rest, base⟩ := A.outsideBase four edge least form paid
  apply increment G C T (A.edges A.pivot) (A.allowance A.pivot + 1) _ res rest base (pivot T rest)
  have dj := disjoint_charge A.components A.dirty _ A.dirtySub A.dirtyDisj
  have rt := disjoint_charge A.components A.roots _ A.rootSub A.rootDisj
  have sum := Finset.sum_erase_add A.components A.allowance hp
  have sumCap : (∑ i ∈ A.components, A.allowance i) ≤ (junk G C).card + 2*(centreless G C).card := by
    simp only [allowance, Finset.sum_add_distrib, ← Finset.mul_sum]
    omega
  omega

theorem finishMarkedFour (A : Allocation G C) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (one : (orN G C \ lam G C).card = 1) (hp : A.pivot ∈ A.components)
    (paid : ∀ i ∈ A.components.erase A.pivot, A.Local i)
    (res : A.edges A.pivot ⊆ Ustar G C) (p : ℕ → Bool → Fin n)
    (labels : ∀ e ∈ A.edges A.pivot, ∃ i < 4, e = s(p i false,p i true))
    (qty : (A.edges A.pivot).card = 4) (capacity : 7 ≤ A.allowance A.pivot + 1)
    {i j : ℕ} (hi : i < 4) (hj : j < 4) (b d : Bool)
    (adj : G.Adj (p i b) (p j d)) (outside : s(p i b,p j d) ∉ A.edges A.pivot) :
    Positive G C := by
  obtain ⟨T, rest, base⟩ := A.outsideBase four edge least form paid
  obtain ⟨l,hl,side,marked⟩ := mark_of_cross G T _ p 4 rest hi hj b d adj outside
  apply increment G C T (A.edges A.pivot) 7 _ res rest base
    (marked_four T _ p labels qty hl side marked)
  have dj := disjoint_charge A.components A.dirty _ A.dirtySub A.dirtyDisj
  have rt := disjoint_charge A.components A.roots _ A.rootSub A.rootDisj
  have sum := Finset.sum_erase_add A.components A.allowance hp
  have sumCap : (∑ i ∈ A.components, A.allowance i) ≤ (junk G C).card + 2*(centreless G C).card := by
    simp only [allowance, Finset.sum_add_distrib, ← Finset.mul_sum]
    omega
  omega

end Allocation
end PEqualNP.Outside.L_meta_4186_aux.Q1Double
