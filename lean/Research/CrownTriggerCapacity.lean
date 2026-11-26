import Research.CrownFirstTrigger
import Research.CrownCollisionLimit

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

private theorem baseline_off (L : List Bool) (h : L.count true = 0) :
    ∀ i, L.getD i false = false := by
  induction L with
  | nil => simp
  | cons b t ih =>
    cases b with
    | true => simp at h
    | false =>
      intro i
      cases i with
      | zero => rfl
      | succ i => exact ih (by simpa using h) i

/-- A fixed set of wires that can trigger the earliest OR on every
two-active diagonal contains at least four members. The choice may be
made separately on each diagonal. -/
theorem crown_trigger_capacity (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (T : Finset ℕ) (hit : ∀ (i : Fin 12) (k : Fin C.gates.length),
      (trueOrFlags C.gates (oneEach i i)).count true = 2 →
      k ∈ activeOrIds C.gates (oneEach i i) →
      (∀ j ∈ activeOrIds C.gates (oneEach i i), k ≤ j) →
      ∃ v ∈ T, v ∈ readAt C.gates 24 k.val ∧ (C.wires (oneEach i i)).getD v false = true) :
    4 ≤ T.card := by
  classical
  let S := Finset.univ.filter (fun i : Fin 12 => 2 ≤ (trueOrFlags C.gates (oneEach i i)).count true)
  have many : 4 ≤ S.card := crown_many_saturated C hm rep size
  let x (i : S) := oneEach i.val i.val
  let A (i : S) := activeOrIds C.gates (x i)
  let z := List.replicate 24 false
  have two (i : S) : (trueOrFlags C.gates (x i)).count true = 2 := by
    have lo := (Finset.mem_filter.mp i.property).2
    have hi := crown_trueOrFlags_le i.val C hm rep
    dsimp only [x]
    omega
  have nz (i : S) : (A i).Nonempty := Finset.card_pos.mp (by
    change 0 < (activeOrIds C.gates (x i)).card
    rw [activeOrIds_card,two]
    decide)
  let gate (i : S) := (A i).min' (nz i)
  have mem (i : S) : gate i ∈ A i := Finset.min'_mem ..
  have least (i : S) (j : Fin C.gates.length) (hj : j ∈ A i) : gate i ≤ j := Finset.min'_le _ _ hj
  have avail (i : S) := hit i.val (gate i) (two i) (mem i) (least i)
  choose v hv hr hon using avail
  have zero := baseline_off _ (crown_allzero_no_or C hm rep size ors)
  have masked (i : S) :
      (maskedWires C.gates (x i)).getD (v i) false = true ∧
      (maskedWires C.gates z).getD (v i) false = false := by
    have xl : (x i).length = 24 := by simp [x,oneEach]
    have onset := (activeOrIds_mem C.gates (x i) (gate i)).mp (mem i)
    have prior (j : ℕ) (hj : j < (gate i).val) : (trueOrFlags C.gates (x i)).getD j false = false := by
      cases H : (trueOrFlags C.gates (x i)).getD j false with
      | false => rfl
      | true =>
        let f : Fin C.gates.length := ⟨j,hj.trans (gate i).isLt⟩
        have lb := least i f ((activeOrIds_mem _ _ f).mpr H)
        exact False.elim (Nat.not_le_of_lt hj lb)
    apply first_parent_masked C.gates (x i) z (by simp [z,xl]) (gate i).val onset prior zero
    · simpa only [xl] using hr i
    · exact hon i
  let inj (i : S) : T := ⟨v i,hv i⟩
  have one : Function.Injective inj := by
    intro i j eq
    have eqv : v i = v j := congrArg Subtype.val eq
    apply Subtype.ext
    exact masked_unique_diagonal C hm (v i) (masked i).2 i.val j.val (masked i).1 (eqv ▸ (masked j).1)
  have bound := Fintype.card_le_of_injective inj one
  exact many.trans (by simpa using bound)

end PEqualNP.Research.MissingCell
