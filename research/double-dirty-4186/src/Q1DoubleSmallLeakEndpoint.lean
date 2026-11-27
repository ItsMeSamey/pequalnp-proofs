import Q1DoubleOutside
import Q1DoubleOneLeakIncrementalCases

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Allocation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.Q1Double

theorem finishSmallOneLeak {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (D : Allocation G C) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (one : (orN G C \ lam G C).card = 1) (hp : D.pivot ∈ D.components)
    (paid : ∀ i ∈ D.components.erase D.pivot, D.Local i)
    (rem : D.edges D.pivot ⊆ Ustar G C) (a b w y : ℕ) (R S H : Finset (Sym2 (Fin n)))
    (partition : D.edges D.pivot = R ∪ S ∪ H) (ha : 2 ≤ a)
    (hy : 3 ≤ y) (exp : 0 < H.card → 2^H.card ≤ y) (opp : 2*S.card ≤ b+w)
    (privateCover : ∀ X : Finset (Fin n),
      (∀ x z, G.Adj x z → s(x,z) ∉ (R ∪ S) → x ∈ X ∨ z ∈ X) →
      ∃ Z, OneLeak.covers (X ∪ Z) R ∧ OneLeak.covers (X ∪ Z) S ∧
        (X ∪ Z).card + R.card + S.card ≤ X.card + (a+b+w))
    (tight : H.card=2 → y=4 →
      R.card ≤ 1 ∧ ∃ F, OneLeak.covers F R ∧ OneLeak.covers F H ∧ F.card ≤ 2)
    (price : a+b+w+y-1 ≤ D.allowance D.pivot+1) : Positive G C := by
  apply D.finishIncremental four edge least form one hp paid rem
  intro T rest
  rw [partition] at rest ⊢
  obtain ⟨K,cr,cs,ch,size⟩ := OneLeak.two_incremental G T a b w y R S H ha hy exp opp rest
    privateCover tight
  refine ⟨K,?_,?_⟩
  · intro x z he
    rcases Finset.mem_union.mp he with e | e
    · rcases Finset.mem_union.mp e with r | s
      · exact cr _ _ r
      · exact cs _ _ s
    · exact ch _ _ e
  · have t := Finset.card_union_le R S
    have v := Finset.card_union_le (R ∪ S) H
    omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Allocation
