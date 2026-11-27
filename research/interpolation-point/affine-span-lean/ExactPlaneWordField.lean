import ExactPlaneModulusTransport
import ExactPlaneIrreducibleSearch
namespace ExactPlaneBinaryArithmetic
open ExactPlaneIrreducibleSearch (poly)
variable {r : ℕ}

noncomputable def encode_word (c : Word r) : Word r ≃ₗ[F] AdjoinRoot (poly c) :=
  wordEquiv (ExactPlaneIrreducibleSearch.monic c) (ExactPlaneIrreducibleSearch.degree c)

theorem encode_word_power (c : Word r) (hr : 0 < r) (x : Word r) (n : ℕ) :
    encode_word c (power c x n) = (encode_word c x)^n := by
  apply wordEquiv_power _ _ hr
  intro i
  rw [ExactPlaneIrreducibleSearch.poly_coeff]
  simp only [ExactPlaneIrreducibleSearch.coeff,dif_pos i.isLt]
  have neg_self : ∀ a : F,a = -a := by decide
  exact neg_self _

#print axioms encode_word_power
end ExactPlaneBinaryArithmetic
