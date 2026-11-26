import Research.CrownDistinctReaders

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- Static output wire indices of OR gates. -/
def orOutputWires : List Gate → ℕ → Finset ℕ
  | [], _ => ∅
  | g::gs, n => if isOrGate g then insert n (orOutputWires gs (n+1))
    else orOutputWires gs (n+1)

private theorem output_range (gs : List Gate) (n a : ℕ) (ha : a ∈ orOutputWires gs n) :
    n ≤ a ∧ a < n + gs.length := by
  induction gs generalizing n with
  | nil => simp [orOutputWires] at ha
  | cons g gs ih =>
    by_cases ho : isOrGate g = true
    · simp only [orOutputWires,ho,↓reduceIte,Finset.mem_insert] at ha
      rcases ha with rfl | rest
      · simp
      · have := ih (n+1) rest
        simp only [List.length_cons]
        omega
    · have h := ih (n+1) (by simpa [orOutputWires,ho] using ha)
      simp only [List.length_cons]
      omega

theorem orOutputWires_card (gs : List Gate) (n : ℕ) :
    (orOutputWires gs n).card = (gs.filter isOrGate).length := by
  induction gs generalizing n with
  | nil => simp [orOutputWires]
  | cons g gs ih =>
    have fresh : n ∉ orOutputWires gs (n+1) := by
      intro h
      have := (output_range gs (n+1) n h).1
      omega
    by_cases ho : isOrGate g = true <;> simp [orOutputWires,ho,fresh,ih]

private theorem readUnion_range (gs : List Gate) (n a : ℕ) (ha : a ∈ readUnion (orInputSets gs n)) :
    a < n + gs.length := by
  induction gs generalizing n with
  | nil => simp [orInputSets,readUnion] at ha
  | cons g gs ih =>
    simp only [List.length_cons]
    by_cases ho : isOrGate g = true
    · simp [orInputSets,ho,readUnion] at ha
      rcases ha with ⟨_,lt⟩ | rest
      · omega
      · have := ih (n+1) rest
        omega
    · have := ih (n+1) (by simpa [orInputSets,ho] using ha)
      omega

theorem or_input_source_budget (C : Circuit) (hm : Monotone2 C) (n : ℕ) :
    (readUnion (orInputSets C.gates n)).card ≤ n + (C.gates.filter CrownDiagonalCharge.isAndGate).length +
      ((readUnion (orInputSets C.gates n)) ∩ orOutputWires C.gates n).card := by
  let r := readUnion (orInputSets C.gates n)
  let o := orOutputWires C.gates n
  let all := Finset.range (n+C.gates.length)
  have rsub : r ⊆ all := fun a ha => Finset.mem_range.mpr (readUnion_range _ _ _ ha)
  have osub : o ⊆ all := fun a ha => Finset.mem_range.mpr (output_range _ _ _ ha).2
  have sub : r \ o ⊆ all \ o := fun a ha => Finset.mem_sdiff.mpr
    ⟨rsub (Finset.mem_sdiff.mp ha).1,(Finset.mem_sdiff.mp ha).2⟩
  have h := Finset.card_le_card sub
  rw [Finset.card_sdiff_of_subset osub] at h
  have hAll : all.card = n+C.gates.length := Finset.card_range _
  have hO : o.card = (C.gates.filter isOrGate).length := orOutputWires_card ..
  have gates := CrownDiagonalCharge.and_or_partition C.gates (fun g hg => (hm g hg).1)
  have part := Finset.card_sdiff_add_card_inter r o
  change r.card ≤ n + (C.gates.filter CrownDiagonalCharge.isAndGate).length + (r ∩ o).card
  omega

theorem or_source_budget (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) :
    (readUnion (orInputSets C.gates 24)).card ≤
      ((readUnion (orInputSets C.gates 24)) ∩ (orOutputWires C.gates 24)).card + 41 := by
  have cap := or_input_source_budget C hm 24
  have hN := CrownDiagonalCharge.crown_size_forty_requires_twenty_three_ors C hm rep size
  have gates := CrownDiagonalCharge.and_or_partition C.gates (fun g hg => (hm g hg).1)
  have hL : C.gates.length ≤ 40 := size
  omega

/-- Under disjoint saturated signatures, at least three different OR outputs
must themselves be read by later OR gates of a size-forty crown circuit. -/
theorem crown_three_or_to_or (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) (i j : Fin 12)
    (twoI : (trueOrFlags C.gates (oneEach i i)).count true = 2)
    (twoJ : (trueOrFlags C.gates (oneEach j j)).count true = 2)
    (dis : Disjoint (activeOrIds C.gates (oneEach i i)) (activeOrIds C.gates (oneEach j j))) :
    3 ≤ ((readUnion (orInputSets C.gates 24)) ∩ (orOutputWires C.gates 24)).card := by
  have hR := disjoint_saturation_forty_four_parents C hm rep ors i j twoI twoJ dis
  have cap := or_source_budget C hm rep size
  omega

/-- Every size-forty crown circuit with at most 23 OR gates has at least
two distinct OR outputs feeding later OR gates. -/
theorem crown_two_or_to_or (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) :
    2 ≤ ((readUnion (orInputSets C.gates 24)) ∩ (orOutputWires C.gates 24)).card := by
  have many := CrownDiagonalCharge.crown_many_saturated C hm rep size
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 <
    (Finset.univ.filter (fun i : Fin 12 =>
      2 ≤ (trueOrFlags C.gates (oneEach i i)).count true)).card by omega)
  have low := (Finset.mem_filter.mp hi).2
  have bal := trueOrFlags_balance C.gates (oneEach i i)
  have f := crown_twelve_falseOrCount i C hm rep
  have hR := saturated_forty_three_parents C hm rep ors i (by omega)
  have cap := or_source_budget C hm rep size
  omega

end PEqualNP.Research.MissingCell
