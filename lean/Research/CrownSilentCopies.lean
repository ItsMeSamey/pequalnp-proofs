import Research.CrownInducedAnd
import Research.CrownRawCharge

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

/-- If no OR fires at w, every wire true at w is insensitive to changes
outside the initially true raw coordinates of w. -/
theorem silent_agreement (gs : List Gate) (w x y : List Bool)
    (lx : x.length = w.length) (ly : y.length = w.length)
    (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (silent : (trueOrFlags gs w).count true = 0)
    (agree : ∀ a, w.getD a false = true → x.getD a false = y.getD a false) :
    ∀ a, ((Circuit.mk gs 0).wires w).getD a false = true →
      ((Circuit.mk gs 0).wires x).getD a false = ((Circuit.mk gs 0).wires y).getD a false := by
  induction gs generalizing w x y with
  | nil => exact agree
  | cons g gs ih =>
    have offs := List.count_eq_zero.mp silent
    change true ∉ (isOrGate g && gateBool g w) :: trueOrFlags gs (advance g w) at offs
    have off : (isOrGate g && gateBool g w) ≠ true := fun h => offs (by simp [h])
    have tail : (trueOrFlags gs (advance g w)).count true = 0 :=
      List.count_eq_zero.mpr (fun hm => offs (List.mem_cons_of_mem _ hm))
    apply ih (advance g w) (advance g x) (advance g y) (by simp [advance_len,lx])
      (by simp [advance_len,ly]) (fun h hh => mono h (List.mem_cons_of_mem _ hh)) tail
    intro a hot
    by_cases small : a < w.length
    · exact (getD_advance_lt _ _ _ (by omega)).trans ((agree a ((getD_advance_lt _ _ _ small).symm.trans hot)).trans
        (getD_advance_lt _ _ _ (by omega)).symm)
    · by_cases eq : a = w.length
      · subst a
        rw [getD_advance_eq] at hot
        rw [←lx,getD_advance_eq,lx,←ly,getD_advance_eq]
        rcases mono g (List.mem_cons_self ..) with hg|hg
        · have all : ∀ j ∈ g.inputs, w.getD j false = true := by simpa [hg,GateOp.eval] using hot
          congr 1
          apply List.map_congr_left
          intro j hj
          exact agree j (all j hj)
        · exact False.elim (off (Bool.and_eq_true_iff.mpr ⟨by simp [isOrGate,hg],hot⟩))
      · rw [getD_missing (by rw [advance_len]; omega)] at hot
        contradiction

theorem silent_cold_is_copy (C : Circuit) (hm : Monotone2 C) (r : Fin 24)
    (silent : (trueOrFlags C.gates (singleInput r)).count true = 0) (a : ℕ)
    (hot : (C.wires (singleInput r)).getD a false = true)
    (cold : (C.wires (List.replicate 24 false)).getD a false = false)
    (y : List Bool) (yl : y.length = 24) :
    (C.wires y).getD a false = y.getD r.val false := by
  have unique (i : ℕ) (h : (singleInput r).getD i false = true) : i = r.val := by
    by_cases hb : i < 24
    · have eq := raw_single_support (Circuit.mk [] 0) (⟨i,hb⟩ : Fin 24) r
      change (singleInput r).getD i false = _ at eq
      have ids : (⟨i,hb⟩ : Fin 24) = r := of_decide_eq_true (eq.symm.trans h)
      exact congrArg Fin.val ids
    · rw [getD_missing (by simp [singleInput];omega)] at h
      contradiction
  have len : (singleInput r).length = 24 := by simp [singleInput]
  have hook := silent_agreement C.gates (singleInput r)
  cases bit : y.getD r.val false with
  | true =>
    have e := hook (singleInput r) y rfl (yl.trans len.symm) (fun g hg => (hm g hg).1) silent
      (fun i h => (unique i h) ▸ h.trans bit.symm) a hot
    exact e.symm.trans hot
  | false =>
    have e := hook (List.replicate 24 false) y (by simp [len]) (yl.trans len.symm)
      (fun g hg => (hm g hg).1) silent (by
        intro i h
        rw [unique i h,bit]
        simp only [List.getD_eq_getElem?_getD,List.getElem?_replicate,ite_eq_left r.isLt,Option.getD_some]) a hot
    exact e.symm.trans cold
end PEqualNP.Research.MissingCell
