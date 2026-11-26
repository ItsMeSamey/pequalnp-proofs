import Research.CrownRawCharge
import Research.CrownLiteralExcess
import Research.CrownDemandArithmetic
namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge
open scoped BigOperators

theorem chargeable_card_le_and (C : Circuit) :
    (Finset.univ.filter (fun k : Fin C.gates.length => chargeable C k)).card ≤
      (C.gates.filter isAndGate).length := by
  classical
  have index_eq (gs : List Gate) :
      (Finset.univ.filter (fun k : Fin gs.length => isAndGate gs[k])).card =
        (gs.filter isAndGate).length := by
    let v : List.Vector Gate gs.length := ⟨gs,rfl⟩
    calc
      _ = gs.countP isAndGate := (List.Vector.countP_toList isAndGate v).symm
      _ = _ := List.countP_eq_length_filter
  rw [←index_eq]
  apply Finset.card_le_card
  intro k hk
  have h := (Finset.mem_filter.mp hk).2
  change chargeable C k = true at h
  have andop : isAndGate C.gates[k] = true := by
    unfold chargeable at h
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).1
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,andop⟩

def crownDemand (C : Circuit) := CrownDemandArithmetic.demand
  (fun i => singletonExcess C (rowPort i)) (fun j => singletonExcess C (colPort j))

theorem crown_demand_as_weight (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23) :
    (crownDemand C : ℚ) = 16 * ∑ p ∈ Finset.univ.filter (fun p : Fin 12 × Fin 12 => p.1 ≠ p.2),
      singletonWeight C (rowPort p.1) * singletonWeight C (colPort p.2) := by
  classical
  have quarter (t : Fin 24) : ((1 + singletonExcess C t : ℕ):ℚ) = 4 * singletonWeight C t := by
    rw [←quarter_eq_one_add_excess C t (literal_count_le_two C hm rep ors t)]
    exact singletonQuarter_eq C t (literal_count_le_two C hm rep ors t)
  let f (i j : Fin 12) := singletonWeight C (rowPort i) * singletonWeight C (colPort j)
  have shape : (∑ p ∈ Finset.univ.filter (fun p : Fin 12 × Fin 12 => p.1 ≠ p.2), f p.1 p.2) =
      ∑ i : Fin 12, ∑ j ∈ Finset.univ.erase i, f i j := by
    rw [Finset.sum_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    have eq : Finset.univ.erase i = Finset.univ.filter (fun j : Fin 12 => i ≠ j) := by
      ext j; simp [ne_comm]
    rw [eq,Finset.sum_filter]
  change (crownDemand C : ℚ) = 16 * ∑ p ∈ Finset.univ.filter (fun p : Fin 12 × Fin 12 => p.1 ≠ p.2), f p.1 p.2
  rw [shape,Finset.mul_sum]
  simp only [crownDemand,CrownDemandArithmetic.demand,Nat.cast_sum,Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [quarter,quarter]
  dsimp [f]
  ring

theorem crown_demand_cap (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) : crownDemand C ≤ 16*17 := by
  classical
  let T := Finset.univ.filter (fun k : Fin C.gates.length => chargeable C k = true)
  have hgate : T.card ≤ 17 := by
    have a := chargeable_card_le_and C
    have b := crown_size_forty_requires_twenty_three_ors C hm rep size
    have p := and_or_partition C.gates (fun g h => (hm g h).1)
    change T.card ≤ _ at a
    change C.gates.length ≤ 40 at size
    omega
  have hcap : (∑ k ∈ T, singletonMass C (operand C k 0) * singletonMass C (operand C k 1)) ≤ 17 := by
    calc
      _ ≤ ∑ _k ∈ T, (1:ℚ) := Finset.sum_le_sum (fun k hk => chargeable_product_le_one C hm k (Finset.mem_filter.mp hk).2)
      _ ≤ 17 := by simpa using (show (T.card:ℚ) ≤ 17 by exact_mod_cast hgate)
  have h := (crown_weighted_edge_charge C hm rep).trans hcap
  have eq := crown_demand_as_weight C hm rep ors
  have rat : (crownDemand C : ℚ) ≤ 16*17 := by linarith
  exact_mod_cast rat

end PEqualNP.Research.MissingCell
