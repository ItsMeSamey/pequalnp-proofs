import ExactPlaneDirectDivision
import ExactPlaneIrreducibleConstructor
namespace ExactPlaneIrreducibleSearch

def fastConstruct (n : ℕ) : Word n :=
  (ExactPlaneDirectDivision.fastFind n).getD (fun _ => 0)

theorem fastConstruct_eq (n : ℕ) (hn : 0<n) : fastConstruct n=construct n := by
  rw [fastConstruct,construct,ExactPlaneDirectDivision.fastFind_eq n hn]

theorem fast_spec (n : ℕ) (hn : 0<n) :
    (poly (fastConstruct n)).Monic ∧ (poly (fastConstruct n)).natDegree=n ∧
    Irreducible (poly (fastConstruct n)) := by
  rw [fastConstruct_eq n hn]
  exact construct_spec n hn

#print axioms fast_spec
end ExactPlaneIrreducibleSearch
