import ShoreComponents

namespace OnePerShore.Upper.Examples
open PEqualNP.Represents

/-- Universal row and two disjoint residual bicliques. -/
def mixed (u : Fin 4) (v : Fin 4) := (49983 : ℕ).testBit (4*u.val+v.val)

/-- The representation has a raw output and uses zero gates. -/
def raw (u : Fin 2) (_ : Fin 2) := decide (u=0)

example : RepSizeAtMost raw 0 := by
  have h := physical_of_biclique_residual raw ⟨0,0,by decide⟩ ⟨1,1,by decide⟩ (by
    unfold BicliqueResidual; decide +kernel)
  exact h

example : RepSizeAtMost mixed 7 := by
  have h := physical_of_biclique_residual mixed ⟨0,0,by decide⟩ ⟨1,3,by decide⟩ (by
    unfold BicliqueResidual; decide +kernel)
  exact h

end OnePerShore.Upper.Examples

#print axioms OnePerShore.Upper.exact_floor_iff
#print axioms OnePerShore.Upper.physical_of_biclique_residual
