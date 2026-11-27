import ExactPlaneIrreducibleSearch
import ExactPlaneIrreducibleExist

namespace ExactPlaneIrreducibleSearch

theorem find_complete (n : ℕ) (hn : 0<n) : ∃ w, find n=some w :=
  find_complete_of_exists hn (ExactPlaneIrreducibleExist.exists_degree n hn)

/-- On positive degrees the fallback branch is unreachable. -/
def construct (n : ℕ) : Word n := (find n).getD (fun _ => 0)

theorem construct_spec (n : ℕ) (hn : 0<n) :
    (poly (construct n)).Monic ∧ (poly (construct n)).natDegree=n ∧
    Irreducible (poly (construct n)) := by
  obtain ⟨w,found⟩ := find_complete n hn
  simpa [construct,found] using find_sound hn found

#print axioms construct_spec
end ExactPlaneIrreducibleSearch
