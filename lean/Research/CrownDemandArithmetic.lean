import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Fin

namespace CrownDemandArithmetic
open scoped BigOperators
abbrev L := Fin 12

def demand (r c : L → ℕ) : ℕ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, (1 + r i) * (1 + c j)

theorem demand_lower (r c : L → ℕ) :
    132 + 11 * (∑ i, (r i + c i)) ≤ demand r c := by
  classical
  have card (i : L) : (Finset.univ.erase i).card = 11 := by simp
  have bound (i j : L) : 1 + r i + c j ≤ (1 + r i) * (1 + c j) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  have row (i : L) : ∑ j ∈ Finset.univ.erase i, (1 + r i + c j) =
      11 + 11 * r i + ∑ j ∈ Finset.univ.erase i, c j := by
    rw [Finset.sum_add_distrib]
    simp [card, Nat.mul_add]
  have col (j : L) : ∑ i : L, (if i ≠ j then c j else 0) = 11 * c j := by
    rw [← Finset.sum_filter]
    have eq : Finset.univ.filter (fun i : L => i ≠ j) = Finset.univ.erase j := by ext; simp
    simp [eq,card]
  have part (i : L) : ∑ j ∈ Finset.univ.erase i, c j =
      ∑ j : L, if i ≠ j then c j else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp [ne_comm]
  have cols : (∑ i, ∑ j ∈ Finset.univ.erase i, c j) = 11 * ∑ j, c j := by
    simp_rw [part]
    rw [Finset.sum_comm]
    simp_rw [col]
    rw [Finset.mul_sum]
  calc
    _ = ∑ i, ∑ j ∈ Finset.univ.erase i, (1 + r i + c j) := by
      simp_rw [row]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, cols]
      simp [Nat.mul_add, Nat.add_assoc]
    _ ≤ demand r c := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => bound i j

theorem impossible_of_excess (r c : L → ℕ) (excess : 13 ≤ ∑ i, (r i + c i))
    (cap : demand r c ≤ 16 * 17) : False := by
  have h := demand_lower r c
  omega

theorem clean_nest_excess (shared nested disjoint silent contaminated excess : ℕ)
    (count : shared + nested + disjoint + silent = 12) (few : shared ≤ 3)
    (injects : contaminated ≤ silent) (within : contaminated ≤ nested)
    (base : (nested - contaminated) * 2 + contaminated + disjoint * 2 + silent * 3 ≤ excess) :
    18 ≤ excess := by omega

theorem one_collision_excess (r c : L → ℕ) (light : Finset L) (many : 7 ≤ light.card)
    (budget : ∀ i ∈ light, 2 ≤ r i + c i) : 14 ≤ ∑ i, (r i + c i) := by
  have h := Finset.sum_le_sum budget
  have sub : (∑ i ∈ light, (r i + c i)) ≤ ∑ i, (r i + c i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  change light.card * 2 ≤ _ at h
  omega

theorem exclude_collision (r c : L → ℕ) (sat : Finset L) (few : sat.card ≤ 5)
    (h : ∀ i ∉ sat, 2 ≤ r i + c i) (cap : demand r c ≤ 16 * 17) : False := by
  have rem : (Finset.univ \ sat).card + sat.card = 12 := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ sat)
  have ex := one_collision_excess r c (Finset.univ \ sat) (by omega)
    (fun i hi => h i (Finset.mem_sdiff.mp hi).2)
  exact impossible_of_excess r c (by omega) cap

end CrownDemandArithmetic
