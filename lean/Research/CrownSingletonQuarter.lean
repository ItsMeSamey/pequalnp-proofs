import Research.CrownSingletonKraft
import Research.CrownIndexedOrValues

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

theorem activeOrIds_mono (C : Circuit) (hm : Monotone2 C) (x y : List Bool) (len : x.length = y.length)
    (le : ∀ a, x.getD a false = true → y.getD a false = true) :
    activeOrIds C.gates x ⊆ activeOrIds C.gates y := by
  intro k hk
  obtain ⟨a,ha,on⟩ := (activeOrIds_iff_final_parent C.gates x k).mp hk
  apply (activeOrIds_iff_final_parent C.gates y k).mpr
  let D : Circuit := ⟨C.gates,a⟩
  have dh : Monotone2 D := hm
  refine ⟨a,len ▸ ha,?_⟩
  exact eval_mono_live D y.length x y dh len rfl (fun p _ => le p) on

theorem trueOrCount_mono (C : Circuit) (hm : Monotone2 C) (x y : List Bool) (len : x.length = y.length)
    (le : ∀ a, x.getD a false = true → y.getD a false = true) :
    (trueOrFlags C.gates x).count true ≤ (trueOrFlags C.gates y).count true := by
  simpa only [activeOrIds_card] using Finset.card_le_card (activeOrIds_mono C hm x y len le)

def literalLabel (t : Fin 24) : Fin 12 := ⟨t.val % 12,Nat.mod_lt _ (by decide)⟩

private theorem raw_inclusion : ∀ (t a : Fin 24), (singleInput t).getD a.val false = true →
    (oneEach (literalLabel t) (literalLabel t)).getD a.val false = true := by decide

theorem literal_active_subset (C : Circuit) (hm : Monotone2 C) (t : Fin 24) :
    activeOrIds C.gates (singleInput t) ⊆ activeOrIds C.gates (oneEach (literalLabel t) (literalLabel t)) := by
  apply activeOrIds_mono C hm _ _ (by simp [singleInput,oneEach])
  intro a
  by_cases ha : a<24
  · exact raw_inclusion t ⟨a,ha⟩
  · rw [getD_missing (by simp [singleInput];omega : (singleInput t).length ≤ a)]
    simp

theorem literal_count_le_diagonal (C : Circuit) (hm : Monotone2 C) (t : Fin 24) :
    (trueOrFlags C.gates (singleInput t)).count true ≤
      (trueOrFlags C.gates (oneEach (literalLabel t) (literalLabel t))).count true := by
  simpa only [activeOrIds_card] using Finset.card_le_card (literal_active_subset C hm t)

def singletonQuarter {n : ℕ} (C : Circuit) (t : Fin n) : ℕ :=
  4 / 2^((trueOrFlags C.gates (singleInput t)).count true)

theorem literal_count_le_two (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23) (t : Fin 24) :
    (trueOrFlags C.gates (singleInput t)).count true ≤ 2 := by
  have h := literal_count_le_diagonal C hm t
  have d := crown_trueOrFlags_le (literalLabel t) C hm rep
  omega

theorem singletonQuarter_eq {n : ℕ} (C : Circuit) (t : Fin n)
    (cap : (trueOrFlags C.gates (singleInput t)).count true ≤ 2) :
    (singletonQuarter C t : ℚ) = 4 * singletonWeight C t := by
  let k := (trueOrFlags C.gates (singleInput t)).count true
  change (↑(4 / 2^k : ℕ) : ℚ) = 4*(1/2:ℚ)^k
  change k ≤ 2 at cap
  interval_cases k <;> norm_num

theorem singletonQuarter_cases {n : ℕ} (C : Circuit) (t : Fin n)
    (cap : (trueOrFlags C.gates (singleInput t)).count true ≤ 2) :
    singletonQuarter C t = 1 ∨ singletonQuarter C t = 2 ∨ singletonQuarter C t = 4 := by
  unfold singletonQuarter
  generalize (trueOrFlags C.gates (singleInput t)).count true = k at cap ⊢
  interval_cases k <;> decide

theorem singleton_quarter_capacity {n : ℕ} (C : Circuit) (hm : Monotone2 C) (a : ℕ)
    (off : (C.wires (List.replicate n false)).getD a false = false)
    (cap : ∀ t : Fin n, (trueOrFlags C.gates (singleInput t)).count true ≤ 2) :
    ∑ t ∈ Finset.univ.filter (fun t : Fin n => (C.wires (singleInput t)).getD a false),
      singletonQuarter C t ≤ 4 := by
  let S := Finset.univ.filter (fun t : Fin n => (C.wires (singleInput t)).getD a false)
  have bound : (∑ t ∈ S, singletonWeight C t) ≤ 1 := singleton_weight_capacity C hm a off
  have rat : (∑ t ∈ S, (singletonQuarter C t : ℚ)) ≤ 4 := by
    calc
      _ = ∑ t ∈ S, 4 * singletonWeight C t := Finset.sum_congr rfl (fun t _ => singletonQuarter_eq C t (cap t))
      _ = 4 * ∑ t ∈ S, singletonWeight C t := (Finset.mul_sum ..).symm
      _ ≤ 4 := by linarith
  change (∑ t ∈ S, singletonQuarter C t) ≤ 4
  exact_mod_cast rat

end PEqualNP.Research.MissingCell
