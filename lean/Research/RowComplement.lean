import Research.MissingCellRigidity

namespace PEqualNP.Research.RowComplement
open PEqualNP.Research.MissingCell PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity

def rowComplement (k : ℕ) : Fin (k+1) → Fin (k+1) → Bool :=
  fun u _ => decide (u ≠ 0)

def rowNot (k : ℕ) : Circuit :=
  ⟨[⟨.not, [0]⟩], (k+1)+(k+1)⟩

theorem rowNot_rep (k : ℕ) : Represents (rowComplement k) (rowNot k) := by
  intro u v
  have hl : (oneEach u v).length = (k+1)+(k+1) := by simp [oneEach]; omega
  have h0 : (oneEach u v).getD 0 false = decide ((0 : Fin (k+1)) = u) := by
    simp [oneEach, List.getD_eq_getElem?_getD]
  change (advance ⟨.not,[0]⟩ (oneEach u v)).getD ((k+1)+(k+1)) false = _
  rw [←hl, getD_advance_eq]
  simp only [List.map_cons,List.map_nil, GateOp.eval, h0, rowComplement]
  by_cases h : u = 0
  · simp [h]
  · simp [h, Ne.symm h]

theorem rowCost (k : ℕ) (D : Circuit) (hm : Monotone2 D)
    (hr : Represents (rowComplement k) D) : k ≤ D.size + 1 := by
  let S := live D.gates ((k+1)+(k+1)) D.output
  have h := mixed_support (rowComplement k) S (Finset.univ.erase 0) ∅
    (by
      intro u hu
      refine ⟨0,0,?_,?_⟩
      · simp [rowComplement, (Finset.mem_erase.mp hu).1]
      · simp [rowComplement])
    (by simp)
    (by
      intro u v w z h ht
      rw [←hr w z]
      apply eval_mono_live D ((k+1)+(k+1)) (oneEach u v) (oneEach w z) hm
        (by simp [oneEach]; omega) (by simp [oneEach]; omega) h
      simpa [hr u v] using ht)
  have hc := live_card D.gates ((k+1)+(k+1)) D.output (fun g hg => (hm g hg).2)
  have hk : k ≤ S.card := by simpa using h
  exact hk.trans hc

end PEqualNP.Research.RowComplement

open PEqualNP.Research.RowComplement

theorem PEqualNP.Outside.L_meta_19316 : ¬ ∃ a b : ℕ, ∀ (n : ℕ) (A : Fin n → Fin n → Bool) (s : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → PEqualNP.Represents.Represents A C → PEqualNP.Represents.RepSizeAtMost A (a * s + b) := by
  rintro ⟨a,b,h⟩
  let k := a+b+2
  obtain ⟨D, hm, hs, hr⟩ := h (k+1) (rowComplement k) 1 (rowNot k)
    (by simp [rowNot, PEqualNP.MetaComplexity.FanInTwo])
    (by change 1 ≤ 1; rfl) (rowNot_rep k)
  have hl := rowCost k D hm hr
  dsimp [k] at hl
  omega
