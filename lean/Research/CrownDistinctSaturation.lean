import Research.CrownZeroSignature
import Research.CrownZeroOrNormalize

namespace CrownDiagonalCharge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.Research.MissingCell

theorem crown_positive_signature_at_most_two (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (b : List Bool) (positive : 0 < b.count true) :
    (Finset.univ.filter (fun i : Fin 12 => trueOrFlags C.gates (oneEach i i) = b)).card ≤ 2 := by
  apply nonbaseline_signature_at_most_two
  · exact hm
  · intro eq
    rw [eq] at positive
    change 0 < (trueOrFlags C.gates (List.replicate 24 false)).count true at positive
    have hz := crown_allzero_no_or C hm rep size ors
    omega

theorem crown_distinct_saturated_signatures (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) :
    ∃ i j : Fin 12,
      (trueOrFlags C.gates (oneEach i i)).count true = 2 ∧
      (trueOrFlags C.gates (oneEach j j)).count true = 2 ∧
      trueOrFlags C.gates (oneEach i i) ≠ trueOrFlags C.gates (oneEach j j) := by
  classical
  let sig := fun i : Fin 12 => trueOrFlags C.gates (oneEach i i)
  let S := Finset.univ.filter (fun i => 2 ≤ (sig i).count true)
  have many : 4 ≤ S.card := crown_many_saturated C hm rep size
  have sat (i : Fin 12) (hi : i ∈ S) : (sig i).count true = 2 := by
    have pos := (Finset.mem_filter.mp hi).2
    have upper := crown_trueOrFlags_le i C hm rep
    change (sig i).count true ≤ _ at upper
    omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have wi := sat i hi
  have bound := crown_positive_signature_at_most_two C hm rep size ors (sig i) (by omega)
  by_contra! missing
  have sub : S ⊆ Finset.univ.filter (fun a => sig a = sig i) := by
    intro j hj
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (missing i j wi (sat j hj)).symm⟩
  have hc := Finset.card_le_card sub
  change (Finset.univ.filter (fun a => sig a = sig i)).card ≤ 2 at bound
  omega

end CrownDiagonalCharge
