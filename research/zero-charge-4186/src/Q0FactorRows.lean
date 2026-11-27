import Q0Factor

namespace PEqualNP.Outside.L_meta_4186_aux.Q0.Factor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

noncomputable def rowOf (g j : ℕ) : Row := by
  classical
  exact ⟨if j = g then .source else if j ∈ orT G C then .cleanOr else
    if (gateAt C j).op = .and then .product else .disjunction,
    opnd C j 0, opnd C j 1⟩

noncomputable def rowsOf (g : ℕ) : List Row :=
  (List.range C.gates.length).map (rowOf G C g)

noncomputable def doneLayout (g : ℕ) : Layout n :=
  (rowsOf G C g).foldl next (seed n)

end PEqualNP.Outside.L_meta_4186_aux.Q0.Factor
