import IncidenceResidualLower
namespace IncidenceResidualPair
open IncidenceResidualCut IncidenceResidualPath IncidenceResidualPorts

/-- Exact singleton and unordered-pair tests suffice. For different shores
the common-neighbor bound is automatic in a bipartite graph. -/
theorem lower {m k : ℕ} (C : Model m) (N : Fin m → Finset (Fin m))
    (hk : 1<k) (deg : ∀ x,k≤(N x).card)
    (overlap : ∀ x r,r≠x → (N x ∩ N r).card≤1)
    (neg : ∀ x,({x}:Mask m)∉C.X C.out)
    (pairs : ∀ x y,({x,y}:Mask m)∈C.X C.out ↔ y∈N x)
    (live : ∀ i<m+C.s,0<readers C.g C.s C.out i) :
    2*m-1-(2*m)/(k+1)≤C.s := by
  apply IncidenceResidualLower.lower C (k:=k) _ hk live
  refine ⟨N,deg,neg,fun x y hy=>(pairs x y).2 hy,?_⟩
  intro x r ne
  have notsub : ¬N x⊆N r := by
    intro h
    have eq : N x∩N r=N x := Finset.inter_eq_left.mpr h
    have small := overlap x r ne
    rw [eq] at small
    have := deg x
    omega
  obtain ⟨y,hy,no⟩ := Finset.not_subset.mp notsub
  exact ⟨y,hy,fun hit=>no ((pairs r y).1 hit)⟩

#print axioms lower
end IncidenceResidualPair
