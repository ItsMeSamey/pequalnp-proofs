import OriginalCircuitCapacity

namespace SignedTrace
open PEqualNP.CircuitLowerBounds ScalarFork.PhysicalLiveIncidence PhysicalExceptional
open scoped BigOperators

private theorem charge_indicator (C : Circuit) (n w : Nat) :
    (if binCharge C n w = 1 then 1 else 0) = binCharge C n w := by
  unfold binCharge
  cases h : gateAt C n w with
  | none => decide
  | some g => cases hop : g.op <;> simp [hop]

private theorem charged_lookup {C : Circuit} {n w : Nat} (h : binCharge C n w = 1) :
    n ≤ w ∧ ∃ g, C.gates[w-n]? = some g ∧ (g.op = .and ∨ g.op = .or) := by
  by_cases raw : w < n
  · simp [binCharge,gateAt,raw] at h
  · refine ⟨by omega,?_⟩
    cases hg : C.gates[w-n]? with
    | none => simp [binCharge,gateAt,raw,hg] at h
    | some g =>
      refine ⟨g,rfl,?_⟩
      cases hop : g.op <;> simp_all [binCharge,gateAt]

theorem live_charge_le_size (C : Circuit) (n : Nat) :
    (∑ w ∈ vertices C n, binCharge C n w) + (inverters C n).card ≤ C.size := by
  classical
  let A := (vertices C n).filter (fun w => binCharge C n w = 1)
  let U := inverters C n
  have counted : (∑ w ∈ vertices C n, binCharge C n w) = A.card := by
    calc
      _ = ∑ w ∈ vertices C n, (if binCharge C n w = 1 then 1 else 0) := by
        exact Finset.sum_congr rfl (fun w _ => (charge_indicator C n w).symm)
      _ = _ := by simpa only [Nat.cast_id,A] using
        (Finset.sum_boole (R := Nat) (fun w => binCharge C n w = 1) (vertices C n))
  have hinv {w : Nat} (hw : w ∈ U) :
      w < n+C.gates.length ∧ n ≤ w ∧ (C.gates[w-n]?).map Gate.op = some .not := by
    have h := Finset.mem_filter.mp hw
    exact ⟨Finset.mem_range.mp h.1,h.2.1,h.2.2.2⟩
  have hbin {w : Nat} (hw : w ∈ A) :
      n ≤ w ∧ ∃ g, C.gates[w-n]? = some g ∧ (g.op = .and ∨ g.op = .or) :=
    charged_lookup (Finset.mem_filter.mp hw).2
  have dis : Disjoint A U := by
    apply Finset.disjoint_left.mpr
    intro w ha hu
    obtain ⟨_,g,hg,hop⟩ := hbin ha
    have hi := (hinv hu).2.2
    rcases hop with h | h <;> simp [hg,h] at hi
  have bounds {w : Nat} (hw : w ∈ A ∪ U) : n ≤ w ∧ w < n+C.gates.length := by
    rcases Finset.mem_union.mp hw with ha | hu
    · obtain ⟨hn,g,hg,_⟩ := hbin ha
      obtain ⟨idx,_⟩ := List.getElem?_eq_some_iff.mp hg
      exact ⟨hn,by omega⟩
    · exact ⟨(hinv hu).2.1,(hinv hu).1⟩
  have bound : (A ∪ U).card ≤ (Finset.range C.gates.length).card := by
    apply Finset.card_le_card_of_injOn (fun w => w-n)
    · intro w hw
      have hb := bounds hw
      exact Finset.mem_range.mpr (show w-n < C.gates.length by omega)
    · intro w hw v hv heq
      have bw := bounds hw
      have bv := bounds hv
      change w-n=v-n at heq
      omega
  rw [counted]
  change A.card + U.card ≤ C.gates.length
  simpa only [Finset.card_union_of_disjoint dis,Finset.card_range] using bound

end SignedTrace
