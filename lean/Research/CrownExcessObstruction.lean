import Research.CrownArbitraryCharge
import Research.CrownDemandCap
import Research.CrownAggregateExcess

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge
open scoped BigOperators

theorem crown_excess_obstruction (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (q : Fin 24 → ℕ) (pos : ∀ t, 1 ≤ q t)
    (cap : ∀ a, (C.wires (List.replicate 24 false)).getD a false = false →
      weightedWireMass C (fun t => (q t : ℚ)) a ≤ 4)
    (many : 13 ≤ ∑ i : Fin 12, ((q (rowPort i)-1) + (q (colPort i)-1))) : False := by
  classical
  let T := Finset.univ.filter (fun k : Fin C.gates.length => chargeable C k = true)
  have hgate : T.card ≤ 17 := by
    have a := chargeable_card_le_and C
    have b := crown_size_forty_requires_twenty_three_ors C hm rep size
    have p := and_or_partition C.gates (fun g h => (hm g h).1)
    change T.card ≤ _ at a
    change C.gates.length ≤ 40 at size
    omega
  let f (i j : Fin 12) : ℕ := q (rowPort i) * q (colPort j)
  have shape : (∑ p ∈ Finset.univ.filter (fun p : Fin 12 × Fin 12 => p.1 ≠ p.2), f p.1 p.2) =
      ∑ i : Fin 12, ∑ j ∈ Finset.univ.erase i, f i j := by
    rw [Finset.sum_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    have eq : Finset.univ.erase i = Finset.univ.filter (fun j : Fin 12 => i ≠ j) := by
      ext j; simp [ne_comm]
    rw [eq,Finset.sum_filter]
  have bound := crown_arbitrary_quarter_charge C hm rep (fun t => (q t : ℚ)) (by intros; positivity) cap
  have integral : (∑ p ∈ Finset.univ.filter (fun p : Fin 12 × Fin 12 => p.1 ≠ p.2), f p.1 p.2) ≤ 16*T.card := by
    dsimp [f,T]
    exact_mod_cast bound
  rw [shape] at integral
  have raw (t : Fin 24) : 1 + (q t - 1) = q t := by have := pos t; omega
  apply CrownDemandArithmetic.impossible_of_excess _ _ many
  unfold CrownDemandArithmetic.demand
  simp_rw [raw]
  exact integral.trans (by omega)

end PEqualNP.Research.MissingCell
