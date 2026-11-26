import T2SoleOrTopology
import T2SoleOrHotRows
namespace T2SoleOrSplice
open PEqualNP.CircuitLowerBounds ResidualSurplus

/-- Same-arity physical splice theorem, with no external simulation or
counting certificate. The local cleanliness premise is part of EditClaim. -/
theorem physical_edit (n x p : Nat) (pre post : List Gate) (out : Nat) :
    EditClaim n x p pre post out := by
  intro old hx hp clean
  have new := moved_eligible n x p out pre post old hx hp clean
  have shape := ((eligible_iff _ _).mp old).2.2
  have tail : SuffixOK (n+pre.length+1) post :=
    ((ok_append pre (binary .or x p :: post) n).mp shape).2.2
  exact ⟨new,moved_hotRows_lt n x p pre post out hx tail new.1⟩

theorem no_clean_or_at_secondary_minimum (n x p : Nat) (pre post : List Gate) (out : Nat)
    (old : Eligible n ⟨pre ++ binary .or x p :: post,out⟩)
    (minimal : SecondaryMinimum n ⟨pre ++ binary .or x p :: post,out⟩)
    (hx : x<n) (hp : p<n+pre.length)
    (clean : ∀ s : Finset (Fin n), s.card<2 → (run pre (vector s)).getD p false=false) : False :=
  excludes_at_secondary_minimum _ _ _ _ _ _ (physical_edit _ _ _ _ _ _) old minimal hx hp clean

#print axioms physical_edit
#print axioms no_clean_or_at_secondary_minimum
end T2SoleOrSplice
