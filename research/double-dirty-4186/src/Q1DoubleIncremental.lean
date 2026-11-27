import Q1DoubleEndpoint
import Q1PrivateCover

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

/-- The base can include ordinary star centres and selected endpoints on all other
components. Its intersections with the pivot cover are counted only once. -/
theorem increment {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (T : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) (k o : ℕ)
    (sub : E ⊆ Ustar G C)
    (baseCover : ∀ a b, G.Adj a b → s(a,b) ∉ E → a ∈ T ∨ b ∈ T)
    (baseSize : T.card + ((Ustar G C) \ E).card ≤ (tops G C \ centreless G C).card + o)
    (pivot : ∃ S : Finset (Fin n),
      (∀ a b, s(a,b) ∈ E → a ∈ T ∪ S ∨ b ∈ T ∪ S) ∧ (T ∪ S).card + E.card ≤ T.card+k)
    (total : o+k ≤ 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) :
    Positive G C := by
  obtain ⟨S, hS, size⟩ := pivot
  have count := Finset.card_sdiff_add_card_eq_card sub
  refine ⟨T ∪ S, ?_, by omega⟩
  intro a b adj
  by_cases h : s(a,b) ∈ E
  · exact hS a b h
  · exact (baseCover a b adj h).imp (Finset.mem_union_left S) (Finset.mem_union_left S)

/-- Four marked pivot edges cost seven against the existing cover: four edge units
and at most three new vertices. -/
theorem marked_four {n : ℕ} (T : Finset (Fin n)) (E : Finset (Sym2 (Fin n)))
    (p : ℕ → Bool → Fin n) (edges : ∀ e ∈ E, ∃ i < 4, e = s(p i false,p i true))
    (four : E.card = 4) {i : ℕ} (iLt : i < 4) (b : Bool) (precovered : p i b ∈ T) :
    ∃ S : Finset (Fin n), (∀ a b, s(a,b) ∈ E → a ∈ T ∪ S ∨ b ∈ T ∪ S) ∧
      (T ∪ S).card + E.card ≤ T.card+7 := by
  obtain ⟨S,covers,size⟩ := Private.saves_precovered p T iLt b precovered
  refine ⟨S, ?_, by omega⟩
  intro a b he
  obtain ⟨j,hj,eq⟩ := edges _ he
  rcases Sym2.eq_iff.mp eq with same | swap
  · rcases same with ⟨ha,hb⟩
    simpa only [ha,hb] using covers j hj
  · rcases swap with ⟨ha,hb⟩
    simpa only [ha,hb,or_comm] using covers j hj

theorem external_of_base {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (E : Finset (Sym2 (Fin n))) (p : ℕ → Bool → Fin n) (k : ℕ)
    (outside : ∀ a b, G.Adj a b → s(a,b) ∉ E → a ∈ T ∨ b ∈ T)
    (edges : ∀ e ∈ E, ∃ i < k, e = s(p i false,p i true)) :
    ∀ x y, G.Adj x y → x ∈ T ∨ y ∈ T ∨
      ∃ i < k, ∃ z : Bool, x = p i z ∧ y = p i (!z) := by
  intro x y xy
  by_cases he : s(x,y) ∈ E
  · obtain ⟨i,hi,eq⟩ := edges _ he
    rcases Sym2.eq_iff.mp eq with se | sw
    · exact Or.inr (Or.inr ⟨i,hi,false,se.1,se.2⟩)
    · exact Or.inr (Or.inr ⟨i,hi,true,sw.1,sw.2⟩)
  · rcases outside x y xy he with hx | hy
    · exact Or.inl hx
    · exact Or.inr (Or.inl hy)

theorem mark_of_cross {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (E : Finset (Sym2 (Fin n))) (p : ℕ → Bool → Fin n) (k : ℕ)
    (outside : ∀ a b, G.Adj a b → s(a,b) ∉ E → a ∈ T ∨ b ∈ T)
    {i j : ℕ} (hi : i < k) (hj : j < k) (b d : Bool)
    (adj : G.Adj (p i b) (p j d)) (other : s(p i b,p j d) ∉ E) :
    ∃ l < k, ∃ side : Bool, p l side ∈ T := by
  rcases outside _ _ adj other with left | right
  · exact ⟨i,hi,b,left⟩
  · exact ⟨j,hj,d,right⟩

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
