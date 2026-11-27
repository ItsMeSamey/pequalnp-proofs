import Q1DoubleResidual

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.EdgeOwnership

def AcceptPair {n : ℕ} (term : (Fin n → Bool) → Bool) (e : Sym2 (Fin n)) : Prop :=
  ∃ a b : Fin n, e = s(a,b) ∧ term (pairInput a b) = true

theorem partitionProjected {n H : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (E : Finset (Sym2 (Fin n))) (owned : E ⊆ gammaE G C H)
    (P Q : (Fin n → Bool) → Bool) (split : ∀ x, gateVal n C H x = (P x || Q x)) :
    ∃ L R : Finset (Sym2 (Fin n)), Disjoint L R ∧ L ∪ R = E ∧
      L.card + R.card = E.card ∧ (∀ e ∈ L, AcceptPair P e) ∧ (∀ e ∈ R, AcceptPair Q e) := by
  classical
  let L := E.filter (AcceptPair P)
  let R := E \ L
  have sub : L ⊆ E := Finset.filter_subset _ _
  refine ⟨L,R,?_,?_,?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro e hl hr
    exact (Finset.mem_sdiff.mp hr).2 hl
  · ext e
    simp only [Finset.mem_union, R, Finset.mem_sdiff]
    constructor
    · rintro (left | right)
      · exact sub left
      · exact right.1
    · intro he
      by_cases h : e ∈ L
      · exact Or.inl h
      · exact Or.inr ⟨he,h⟩
  · have eq := Finset.card_sdiff_add_card_eq_card sub
    change L.card + (E \ L).card = E.card
    omega
  · exact fun e he => (Finset.mem_filter.mp he).2
  · intro e he
    obtain ⟨base,out⟩ := Finset.mem_sdiff.mp he
    obtain ⟨_,a,b,eq,active⟩ := Finset.mem_filter.mp (owned base)
    rw [split] at active
    have either : P (pairInput a b) = true ∨ Q (pairInput a b) = true := by simpa using active
    rcases either with hp | hq
    · exact (out (Finset.mem_filter.mpr ⟨base, a,b,eq,hp⟩)).elim
    · exact ⟨a,b,eq,hq⟩

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
