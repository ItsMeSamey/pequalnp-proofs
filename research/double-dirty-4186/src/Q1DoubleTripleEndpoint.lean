import Q1DoubleOutside
import Q1DoubleOneLeakCover

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Allocation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.Q1Double

theorem finishTriple {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (D : Allocation G C) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (one : (orN G C \ lam G C).card = 1) (paid : ∀ i ∈ D.components.erase D.pivot, D.Local i)
    (R S H : Finset (Sym2 (Fin n))) (partition : D.edges D.pivot = R ∪ S ∪ H)
    (F : Finset (Fin n)) (cr : OneLeak.covers F R) (cs : OneLeak.covers F S)
    (ch : OneLeak.covers F H) (size : F.card+R.card+S.card+H.card ≤ D.allowance D.pivot+1) :
    Positive G C := by
  apply D.finish four edge least form one
  intro i hi
  by_cases eq : i = D.pivot
  · subst i
    refine ⟨F,?_,?_⟩
    · intro a b he
      rw [partition] at he
      rcases Finset.mem_union.mp he with e | e
      · rcases Finset.mem_union.mp e with r | s
        · exact cr a b r
        · exact cs a b s
      · exact ch a b e
    · have u := Finset.card_union_le R S
      have v := Finset.card_union_le (R ∪ S) H
      simp only [partition, if_pos rfl]
      change F.card + _ ≤ D.allowance D.pivot+1
      omega
  · exact paid i (Finset.mem_erase.mpr ⟨eq,hi⟩)

theorem finishLargeOneLeak {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (D : Allocation G C) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (one : (orN G C \ lam G C).card = 1) (paid : ∀ i ∈ D.components.erase D.pivot, D.Local i)
    (p : OneLeak.Profile) (hk : 3 ≤ p.k) (hz : 1 ≤ p.z) (hb : 2 ≤ p.b) (hw : 1 ≤ p.w)
    (ar : 2^p.r ≤ p.k+p.x+p.w) (bs : 2^p.s ≤ p.b+p.w) (yh : 2^p.h ≤ p.k+p.z)
    (R S H : Finset (Sym2 (Fin n))) (partition : D.edges D.pivot = R ∪ S ∪ H)
    (rc : R.card=p.r) (sc : S.card=p.s) (hc : H.card=p.h)
    (armExt : ∃ i ∈ OneLeak.pairOptions (p.k+p.x+p.w) (p.k+p.z) p.k p.r p.h,
       ∃ F, OneLeak.covers F R ∧ OneLeak.covers F H ∧ F.card+i ≤ p.r+p.h)
    (armArm : ∃ j ∈ OneLeak.pairOptions (p.k+p.x+p.w) (p.b+p.w) p.w p.r p.s,
       ∃ F, OneLeak.covers F R ∧ OneLeak.covers F S ∧ F.card+j ≤ p.r+p.s)
    (exactFour : p.k=3 → p.k+p.z=4 → p.h=2 → p.r=0)
    (price : p.budget ≤ D.allowance D.pivot+1) : Positive G C := by
  obtain ⟨F,cr,cs,ch,sz⟩ := OneLeak.large_cover p hk hz hb hw ar bs yh R S H rc sc hc armExt armArm exactFour
  exact D.finishTriple four edge least form one paid R S H partition F cr cs ch (by omega)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Allocation
