import Q0Readers

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Pure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def NoDirtyOr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  ∀ {j r : ℕ}, j ∈ junk G C → r < C.gates.length → n+j ∈ (gateAt C r).inputs →
    (gateAt C r).op ≠ GateOp.or

end PEqualNP.Outside.L_meta_4186_aux.Q1Pure
