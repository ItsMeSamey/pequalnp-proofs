import ThreeNameSplitCircuit
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.BigOperators.Pi

namespace ThreeNameIncidenceRank
open scoped BigOperators
variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]

/-- Replace one circuit column by a unit vector. Its odd coordinate sum
isolates its coefficient, and every remaining proper subset is independent. -/
theorem circuit_card_le (col : E → V → ZMod 2) (v₀ : V)
    (evenCol : ∀ e, ∑ v, col e v = 0)
    (hc : ThreeNameSplitCircuit.Circuit col Finset.univ) :
    Fintype.card E ≤ Fintype.card V := by
  obtain ⟨e₀, _⟩ := hc.1
  let tagged : E → V → ZMod 2 := fun e =>
    if e = e₀ then (fun v => if v = v₀ then 1 else 0) else col e
  have parity (e : E) : (∑ v, tagged e v) = if e = e₀ then 1 else 0 := by
    by_cases h : e = e₀
    · simp [tagged, h]
    · simp [tagged, h, evenCol]
  have li : LinearIndependent (ZMod 2) tagged := by
    apply Fintype.linearIndependent_iff.mpr
    intro g hg i
    let S := Finset.univ.filter (fun e => g e ≠ 0)
    have bits : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    have zeroS : (∑ e ∈ S, tagged e) = 0 := by
      rw [← hg]
      dsimp only [S]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      rcases bits (g e) with h|h <;> simp [h]
    have trace : (∑ e ∈ S, ∑ v, tagged e v) = 0 := by
      rw [Finset.sum_comm]
      calc
        _ = ∑ v : V, (∑ e ∈ S, tagged e) v := by simp only [Finset.sum_apply]
        _ = 0 := by rw [zeroS]; simp
    have hmissing : e₀ ∉ S := by
      intro h
      simp [parity, h] at trace
    have original : (∑ e ∈ S, col e) = 0 := by
      rw [← zeroS]
      apply Finset.sum_congr rfl
      intro e he
      have h : e ≠ e₀ := fun eq => hmissing (eq ▸ he)
      simp [tagged, h]
    by_contra hi
    have mem : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    have eq := hc.2.2 S (Finset.subset_univ _) ⟨i,mem⟩ original
    exact hmissing (eq.symm ▸ Finset.mem_univ e₀)
  simpa only [Module.finrank_fintype_fun_eq_card] using li.fintype_card_le_finrank

def incidence (tail head : E → V) (e : E) (v : V) : ZMod 2 :=
  (if v = tail e then 1 else 0) + (if v = head e then 1 else 0)

theorem incidence_card_le (tail head : E → V)
    (hc : ThreeNameSplitCircuit.Circuit (incidence tail head) Finset.univ) :
    Fintype.card E ≤ Fintype.card V := by
  obtain ⟨e, _⟩ := hc.1
  apply circuit_card_le (incidence tail head) (tail e) _ hc
  intro i
  simpa [incidence, Finset.sum_add_distrib] using (show (1:ZMod 2) + 1 = 0 by decide)

#print axioms incidence_card_le
end ThreeNameIncidenceRank
