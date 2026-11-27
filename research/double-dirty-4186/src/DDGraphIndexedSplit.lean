import DDGraphSplit
import DDIndexedSplit

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98 Indexed
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

theorem graph_indexed_split {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (m : ℕ) (d : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) :
    let p := splitCuts n C (orT G C) m
    let k := C.size
    ∃ (z : SplitData G C m) (D : Circuit) (a b w : Origin × ℕ) (tail : List Gate),
      ref (build n C p k) (n+z.a) = some a ∧ ref (build n C p k) (n+z.b) = some b ∧
      ref (build n C p k) (n+z.t) = some w ∧
      D.gates = (build n C p k).gates ++ (⟨.and,[a.2,w.2]⟩ :: ⟨.and,[b.2,w.2]⟩ :: tail) ∧
      IsAO2 n D ∧ D.size ≤ C.size+1 ∧
      wireVal n D (n+rank n C p k) = join true (gateVal n C z.a) z.w ∧
      wireVal n D (n+(rank n C p k+1)) = join true (gateVal n C z.b) z.w ∧
      circuitFun n D = circuitFun n C := by
  dsimp only
  obtain ⟨z⟩ := split_data G C m d edge least form
  have ha : z.a < C.size := Finset.mem_range.mp (Finset.mem_filter.mp z.aJunk).1
  have hb : z.b < C.size := Finset.mem_range.mp (Finset.mem_filter.mp z.bJunk).1
  have ht : z.t < C.size := Finset.mem_range.mp (Finset.mem_filter.mp z.top).1
  refine ⟨z,?_⟩
  apply actual_split C _ least.1 (k:=C.size) le_rfl
    ⟨n+z.a,by omega⟩ ⟨n+z.b,by omega⟩ ⟨n+z.t,by omega⟩ _ _ _ z.other
    z.leftSlot z.rightSlot z.guardSlot _ _ z.agree
  · intro f hf
    obtain ⟨i,top,slot⟩ := z.retained f hf
    have hi : i<C.size := Finset.mem_range.mp (Finset.mem_filter.mp top).1
    exact ⟨⟨n+i, by omega⟩,slot⟩
  · have budget := mixer_split_budget d edge least
    have count := z.count
    omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
