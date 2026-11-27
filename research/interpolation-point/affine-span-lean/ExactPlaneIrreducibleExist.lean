import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement

namespace ExactPlaneIrreducibleExist

theorem exists_degree (n : ℕ) (hn : 0 < n) :
    ∃ p : Polynomial (ZMod 2), p.Monic ∧ p.natDegree = n ∧ Irreducible p := by
  let K := GaloisField 2 n
  letI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨a, ha⟩ := Field.exists_primitive_element_of_finite_top (ZMod 2) K
  have hi : IsIntegral (ZMod 2) a := IsIntegral.of_finite _ _
  refine ⟨minpoly (ZMod 2) a, minpoly.monic hi, ?_, minpoly.irreducible hi⟩
  rw [← IntermediateField.adjoin.finrank hi, ha]
  exact IntermediateField.topEquiv.toLinearEquiv.finrank_eq.trans (GaloisField.finrank 2 hn.ne')

#print axioms exists_degree
end ExactPlaneIrreducibleExist
