import Research.CrownIndexedOrReads

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private theorem wires_preserve_prefix (gs : List Gate) (w : List Bool) (a : ℕ) (ha : a < w.length) :
    ((Circuit.mk gs 0).wires w).getD a false = w.getD a false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change ((Circuit.mk gs 0).wires (advance g w)).getD a false = _
    rw [ih _ (by rw [advance_len]; omega),getD_advance_lt g w a ha]

/-- The truth of an indexed OR is read from its valid parents on the final
wire list. A forward or missing input read at gate time contributes false. -/
theorem flag_iff_final_parent (gs : List Gate) (w : List Bool) (k : ℕ) :
    (trueOrFlags gs w).getD k false = true ↔
      ∃ a ∈ readAt gs w.length k, ((Circuit.mk gs 0).wires w).getD a false = true := by
  induction gs generalizing w k with
  | nil => simp [trueOrFlags,readAt,List.getD_eq_getElem?_getD]
  | cons g gs ih =>
    cases k with
    | succ k =>
      change (trueOrFlags gs (advance g w)).getD k false = true ↔
        ∃ a ∈ readAt gs (w.length+1) k, ((Circuit.mk gs 0).wires (advance g w)).getD a false = true
      simpa only [advance_len] using ih (advance g w) k
    | zero =>
      by_cases ho : isOrGate g = true
      · have op : g.op = .or := by cases hg : g.op <;> simp_all [isOrGate]
        simp only [trueOrFlags,List.getD_cons_zero,ho,Bool.true_and,op,GateOp.eval,List.any_eq_true,
          List.mem_map,id_eq,readAt,orReads,↓reduceIte,Finset.mem_filter,List.mem_toFinset]
        constructor
        · rintro ⟨_,⟨a,am,rfl⟩,ha⟩
          have lt : a < w.length := by
            by_contra! bad
            rw [getD_missing bad] at ha
            contradiction
          exact ⟨a,⟨am,lt⟩,(wires_preserve_prefix (g::gs) w a lt).trans ha⟩
        · rintro ⟨a,⟨am,lt⟩,ha⟩
          exact ⟨_,⟨a,am,rfl⟩,(wires_preserve_prefix (g::gs) w a lt).symm.trans ha⟩
      · simp [trueOrFlags,readAt,orReads,ho]

theorem activeOrIds_iff_final_parent (gs : List Gate) (w : List Bool) (i : Fin gs.length) :
    i ∈ activeOrIds gs w ↔
      ∃ a ∈ readAt gs w.length i.val, ((Circuit.mk gs 0).wires w).getD a false = true :=
  (activeOrIds_mem gs w i).trans (flag_iff_final_parent gs w i.val)

theorem activeOrIds_signed_reads (gs : List Gate) (w : List Bool)
    (fanin : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ on : ℕ → Prop, ∀ i : Fin gs.length,
      (readAt gs w.length i.val).card ≤ 2 ∧
      (i ∈ activeOrIds gs w → ∃ a ∈ readAt gs w.length i.val, on a) ∧
      (i ∉ activeOrIds gs w → ∀ a ∈ readAt gs w.length i.val, ¬ on a) := by
  refine ⟨fun a => ((Circuit.mk gs 0).wires w).getD a false = true, ?_⟩
  intro i
  have h := activeOrIds_iff_final_parent gs w i
  exact ⟨readAt_card_le_two _ _ _ fanin,h.mp,fun no a ha on => no (h.mpr ⟨a,ha,on⟩)⟩

end PEqualNP.Research.MissingCell
