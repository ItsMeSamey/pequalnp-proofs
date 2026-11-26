import Research.CrownSingletonQuarter
import Research.CrownArbitraryCharge
import Research.CrownDisjointSingletonWires
import Research.CrownNestedSingleton

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

def cleanQuarter (C : Circuit) (clean : Finset (Fin 24)) (t : Fin 24) : Nat :=
  if t ∈ clean then 2 else singletonQuarter C t

/-- Doubling the early literal's quarter weight at every clean nest preserves
the capacity of every zero-false wire. The trace separation condition says
that only the sibling can share a firing OR with the early literal. -/
theorem clean_weighted_capacity (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23)
    (clean : Finset (Fin 24)) (sibling : Fin 24 → Fin 24)
    (separate : ∀ t ∈ clean, ∀ q, q ≠ t → q ≠ sibling t →
      Disjoint (activeOrIds C.gates (singleInput t)) (activeOrIds C.gates (singleInput q)))
    (other : ∀ t ∈ clean, singletonQuarter C (sibling t) ≤ 2)
    (i : Nat) (cold : (C.wires (List.replicate 24 false)).getD i false = false) :
    weightedWireMass C (fun t => (cleanQuarter C clean t : ℚ)) i ≤ 4 := by
  let S := Finset.univ.filter (fun t : Fin 24 => (C.wires (singleInput t)).getD i false)
  have old : ∑ t ∈ S, singletonQuarter C t ≤ 4 :=
    singleton_quarter_capacity C hm i cold (literal_count_le_two C hm rep ors)
  have result : ∑ t ∈ S, cleanQuarter C clean t ≤ 4 := by
    apply CrownNestedSingleton.clean_reweight_cap S clean sibling _ _ old
    · exact fun t _ ht => by simp [cleanQuarter,ht]
    · intro t ht hc q hq
      by_contra missing
      have qt : q ≠ t := fun e => missing (e ▸ Finset.mem_insert_self ..)
      have qb : q ≠ sibling t := fun e => missing (e ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have ht' := (Finset.mem_filter.mp ht).2
      have hq' := (Finset.mem_filter.mp hq).2
      have exclusion := clean_pair_excludes_wires C hm t q qt.symm (by
        intro k kt kq
        by_cases valid : k < C.gates.length
        · exact Finset.disjoint_left.mp (separate t hc q qt qb)
            ((activeOrIds_mem _ _ ⟨k,valid⟩).mpr kt) ((activeOrIds_mem _ _ ⟨k,valid⟩).mpr kq)
        · rw [getD_missing (by rw [trueOrFlags_length]; omega :
            (trueOrFlags C.gates (nestSingleton t)).length ≤ k)] at kt
          contradiction) i cold ht'
      exact Bool.noConfusion (exclusion.symm.trans hq')
    · intro t _ h
      simp only [cleanQuarter,ite_eq_left h,le_refl,true_and]
      split
      · exact Nat.le_refl _
      · exact other t h
  change (∑ t ∈ S, (cleanQuarter C clean t : ℚ)) ≤ 4
  rw [← Nat.cast_sum]
  exact_mod_cast result

end PEqualNP.Research.MissingCell
