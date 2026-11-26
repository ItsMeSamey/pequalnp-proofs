import PEqualNP.Defs.TopForm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
private def E : List (Fin 11 × Fin 11) := [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
private def negatives : List Nat := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]
private abbrev graph := edgeGraph 11 (E.map fun e => (e.1.val, e.2.val))
private def C : Circuit := { gates := [⟨.or, [6, 7]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [4, 15]⟩, ⟨.and, [13, 12]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [3, 18]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [2, 16]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [10, 22]⟩, ⟨.and, [11, 20]⟩, ⟨.and, [17, 23]⟩, ⟨.or, [9, 26]⟩, ⟨.and, [19, 27]⟩, ⟨.or, [28, 25]⟩, ⟨.or, [29, 24]⟩, ⟨.or, [30, 14]⟩], output := 31 }

theorem near8032Rows :
    C.gates.length = 21 ∧
    (∀ e ∈ E, C.eval (List.ofFn (pairInput e.1 e.2)) = decide (e ≠ (1, 4))) ∧
    (∀ m ∈ negatives, C.eval (List.ofFn fun i : Fin 11 => m.testBit i.val) = false) := by
  decide +kernel

private theorem dirty7 : 7 ∈ junk graph C := by
  apply Finset.mem_filter.mpr
  refine ⟨by decide, rfl, by decide, fun i : Fin 11 => (1546 : Nat).testBit i.val, by decide +kernel, by decide +kernel⟩
private theorem dirty10 : 10 ∈ junk graph C := by
  apply Finset.mem_filter.mpr
  refine ⟨by decide, rfl, by decide, fun i : Fin 11 => (29 : Nat).testBit i.val, by decide +kernel, by decide +kernel⟩
private theorem dirty15 : 15 ∈ junk graph C := by
  apply Finset.mem_filter.mpr
  refine ⟨by decide, rfl, by decide, fun i : Fin 11 => (15 : Nat).testBit i.val, by decide +kernel, by decide +kernel⟩
theorem near8032Junk : 3 ≤ (junk graph C).card := by
  have sub : ({7, 10, 15} : Finset ℕ) ⊆ junk graph C := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact dirty7
    · exact dirty10
    · exact dirty15
  exact (show 3 ≤ ({7, 10, 15} : Finset ℕ).card by decide).trans (Finset.card_le_card sub)
