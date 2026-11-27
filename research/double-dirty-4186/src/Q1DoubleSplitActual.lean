import Q1DoubleSplitCost
import Q1DoubleTopology

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq

theorem mixer_split_budget {n m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (D : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) :
    expense (seed n) (rows n C (splitCuts n C (orT G C) m) C.size) + 2 + (orT G C).card ≤ C.size := by
  have hf : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x := fun x => congrFun least.2.1 x
  have hL : Least n C := ⟨AO_of_IsAO2 n C least.1, fun A hA agree =>
    least.2.2 A (IsAO2_of_AO n A hA) (funext fun x => (agree x).trans (hf x))⟩
  obtain ⟨_, hout⟩ := least_out n C hL
    (by obtain ⟨x,hx⟩ := gf_true n G edge; exact ⟨x,(hf x).trans hx⟩)
    (by intro u; obtain ⟨x,hu,hx⟩ := gf_var n G u; exact ⟨x,hu,(hf x).trans hx⟩)
  obtain ⟨hm,_,dirty⟩ := mixer_info D
  have hnout : n+m ≠ C.output := by
    intro eq
    apply dirty
    intro x hx
    change W n C x (n+m) = true at hx
    rw [eq] at hx
    exact (hf x).symm.trans hx
  obtain ⟨r,lt,rb,hin⟩ := least_read n C hL hout m (by omega)
  apply split_budget C (orT G C) m r (Finset.filter_subset _ _) lt rb
  · exact fun h => dirty (Finset.mem_filter.mp h).2.2
  · exact fun h => no_mixer_or D least.1 rb hin (Finset.mem_filter.mp h).2.1
  · rcases Q0.reader_pin least.1 rb hin with h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
