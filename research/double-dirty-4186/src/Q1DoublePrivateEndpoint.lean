import Q1DoubleOutside
import Q1PrivateComplete

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Allocation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.Q1Double

theorem finishPrivate {n a b w r s : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (D : Allocation G C) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (one : (orN G C \ lam G C).card = 1) (present : D.pivot ∈ D.components)
    (paid : ∀ i ∈ D.components.erase D.pivot, D.Local i) (res : D.edges D.pivot ⊆ Ustar G C)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hw : 1 ≤ w)
    {A : Fin a → Private.Clause n} {B : Fin b → Private.Clause n} {W : Fin w → Private.Clause n}
    (P : Private.Batch G C A W r) (Q : Private.Batch G C B W s)
    (p : ℕ → Bool → Fin n) (hp : ∀ i k, p i.val k = P.pt i k)
    (hq : ∀ j k, p (r+j.val) k = Q.pt j k)
    (labels : Fin (r+s) ≃ ↥(D.edges D.pivot))
    (labelEq : ∀ i, (labels i).val = s(p i.val false, p i.val true))
    (price : a+b+w ≤ D.allowance D.pivot + 1) : Positive G C := by
  classical
  have exactCard : (D.edges D.pivot).card = r+s := by
    simpa using (Fintype.card_congr labels).symm
  have enumerates : ∀ e ∈ D.edges D.pivot, ∃ i < r+s, e = s(p i false,p i true) := by
    intro e he
    obtain ⟨i,eq⟩ := labels.surjective ⟨e,he⟩
    exact ⟨i.val,i.isLt,(congrArg Subtype.val eq).symm.trans (labelEq i)⟩
  have exclusive : ∀ i < r+s, ∀ j < r+s, ∀ x y,
      p i x=p j y → p i (!x)=p j (!y) → i=j := by
    intro i hi j hj x y eq mate
    have key : labels ⟨i,hi⟩ = labels ⟨j,hj⟩ := by
      apply Subtype.ext
      rw [labelEq,labelEq]
      cases x <;> cases y <;> simp_all [Sym2.eq_iff]
    exact congrArg Fin.val (labels.injective key)
  apply D.finishIncremental four edge least form one present paid res
  intro T rest
  obtain ⟨S,hS,cost⟩ := Private.zeroLeak four ha hb hw P Q p hp hq T exclusive
    (external_of_base G T _ p (r+s) rest enumerates)
  refine ⟨S,?_,by omega⟩
  intro x y xy
  obtain ⟨i,hi,eq⟩ := enumerates _ xy
  rcases Sym2.eq_iff.mp eq with se | sw
  · simpa only [se.1,se.2] using hS i hi
  · simpa only [sw.1,sw.2,or_comm] using hS i hi

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Allocation
