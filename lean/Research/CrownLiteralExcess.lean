import Research.CrownSingletonQuarter

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

theorem literalLabel_left : ∀ i : Fin 12, literalLabel (Fin.castAdd 12 i) = i := by decide
theorem literalLabel_right : ∀ i : Fin 12, literalLabel (Fin.natAdd 12 i) = i := by decide

def singletonExcess {n : ℕ} (C : Circuit) (t : Fin n) : ℕ := singletonQuarter C t - 1

theorem quarter_eq_one_add_excess {n : ℕ} (C : Circuit) (t : Fin n)
    (cap : (trueOrFlags C.gates (singleInput t)).count true ≤ 2) :
    singletonQuarter C t = 1 + singletonExcess C t := by
  have cases := singletonQuarter_cases C t cap
  unfold singletonExcess
  omega

theorem unsaturated_literal_excess (C : Circuit) (hm : Monotone2 C) (t : Fin 24)
    (light : (trueOrFlags C.gates (oneEach (literalLabel t) (literalLabel t))).count true ≤ 1) :
    1 ≤ singletonExcess C t := by
  have ht := (literal_count_le_diagonal C hm t).trans light
  unfold singletonExcess singletonQuarter
  generalize (trueOrFlags C.gates (singleInput t)).count true = k at ht ⊢
  interval_cases k <;> decide

theorem unsaturated_label_excess (C : Circuit) (hm : Monotone2 C) (i : Fin 12)
    (light : (trueOrFlags C.gates (oneEach i i)).count true ≤ 1) :
    2 ≤ singletonExcess C (Fin.castAdd 12 i) + singletonExcess C (Fin.natAdd 12 i) := by
  have left := unsaturated_literal_excess C hm (Fin.castAdd 12 i) (by rw [literalLabel_left];exact light)
  have right := unsaturated_literal_excess C hm (Fin.natAdd 12 i) (by rw [literalLabel_right];exact light)
  omega

end PEqualNP.Research.MissingCell
