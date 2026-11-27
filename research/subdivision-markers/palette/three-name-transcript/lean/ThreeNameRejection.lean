import ThreeNameRootLift
import ThreeNameChain
import ThreeNameUsedRank
namespace ThreeNameRejection
open scoped BigOperators
open ThreeNameChain ThreeNameSplitCircuit ThreeNameIncidenceRank
variable {E V G : Type*} [DecidableEq E] [AddCommGroup V] [DecidableEq G]

/-- The printed endpoint pairs and labeled kernel equality suffice to
contradict any physical exact-line support through a finite split chain. -/
theorem no_support (p q : Carrier E V) (a b d : E) (l r : E → G) (x : G)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (ha : l a = x ∨ r a = x) (hb : l b = x ∨ r b = x) (hd : l d = x ∨ r d = x)
    (binary : ∀ v : V, v+v=0)
    (path : Path ({a,b,d} : Finset E) p q)
    (kernel : ∀ T ⊆ q.ground, ((∑ i ∈ T, q.col i) = 0 ↔ (∑ i ∈ T, incidence l r i) = 0))
    (rootGround : ({a,b,d} : Finset E) ⊆ p.ground)
    (indep : Independent p.col ({a,b,d} : Finset E)) :
    ¬∃ S ⊆ p.ground, Disjoint ({a,b,d} : Finset E) S ∧
        (∑ i ∈ S, p.col i) = (∑ i ∈ ({a,b,d} : Finset E), p.col i) ∧
        (∀ Q ⊆ S, ∀ P ⊆ ({a,b,d} : Finset E), (∑ i ∈ Q, p.col i) = (∑ i ∈ P, p.col i) →
          (∑ i ∈ P, p.col i) = 0 ∨ (∑ i ∈ P, p.col i) = ∑ i ∈ ({a,b,d} : Finset E), p.col i) := by
  classical
  let R : Finset E := {a,b,d}
  have rn : R.Nonempty := ⟨a,by simp [R]⟩
  have terminal : ¬ Rooted q R := by
    rintro ⟨C,hg,hr,hc⟩
    have gc : Circuit (incidence l r) C :=
      ⟨hc.1,(kernel C hg).mp hc.2.1,fun T ht hn hz =>
        hc.2.2 T ht hn ((kernel T (ht.trans hg)).mpr hz)⟩
    exact circuit_excludes_three l r C gc x a b d hab had hbd hr ha hb hd
  rintro ⟨S,hs,dj,eq,trace⟩
  obtain ⟨C,hC,hR,hc⟩ := ThreeNameRootLift.from_trace p.col R S rn dj binary indep eq trace
  exact rejects rn binary path terminal ⟨C,hC.trans (Finset.union_subset rootGround hs),hR,hc⟩

#print axioms no_support
end ThreeNameRejection
