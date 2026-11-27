import DDIndexedShape
import DDFactorCone
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q1Double Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq

/-- A top outside the mixer cone retains its own AND row and original ID. -/
theorem external_paid {n m j : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (top : j ∈ tops G C) (off : ¬ Influence n C m (n+j)) :
    ∃ g, ins n C (splitCuts n C (orT G C) m) j = some g := by
  let p := splitCuts n C (orT G C) m
  obtain ⟨jl,hand,_⟩ := Finset.mem_filter.mp top
  have hj := Finset.mem_range.mp jl
  have notT : j ∉ orT G C := fun h =>
    GateOp.noConfusion (hand.symm.trans (Finset.mem_filter.mp h).2.1)
  have keep : Kept G C (n+j) := by
    intro i hi eq
    have e : i=j := by omega
    exact notT (e ▸ hi)
  have jm : j ≠ m := by rintro rfl;exact off .source
  have skip : p.omit j = false := by simp [p,splitCuts,jm,notT]
  have present (b : Fin 2) : ∃ z, pin (build n C p j) n C p j b = some z := by
    let w := opnd C j b
    have mem := opnd_mem least.1 hj b
    have wb := least.1.2.1 j hj w mem
    have km := kept_nonclean edge least form hj w keep mem
    have no : ¬ Influence n C m w := fun h => off (.step h hj mem)
    have nm : w ≠ n+m := fun h => no (h.symm ▸ Influence.source)
    have sm := safe_factor G C m edge least form true (fun _ => false)
    have e := agree C least.1 p (fun _ => false) _ sm j (Nat.le_of_lt hj) w wb
      ⟨km,fun h => (no h).elim⟩
    have base := zero_wire C least.1 w (by change w<n+C.gates.length;omega)
    have shp := shape C p least.1 j (Nat.le_of_lt hj) w wb
    cases hv : physicalSlot n C p j w with
    | none => simp [hv,denotation,base] at e
    | some s =>
      cases h : ref (build n C p j) w with
      | none => simp [hv,h] at shp
      | some z =>
        refine ⟨z,?_⟩
        change (if n ≤ w ∧ p.bypass j b = true then none else _) = _
        have cut : p.bypass j b = false := by simpa [p,splitCuts,w] using nm
        simpa [cut] using h
  obtain ⟨a,ha⟩ := present 0
  obtain ⟨b,hb⟩ := present 1
  change ∃ g, ins n C p j = some g
  simp [ins,ha,hb,skip,instruction]
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
