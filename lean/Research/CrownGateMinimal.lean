import Research.CrownMaskedRigidity
import PEqualNP.Outside.L_meta_2668

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_2668

/-- Size minimality is taken among representations obeying the same OR budget. -/
def crownSizeMinimal (C : Circuit) : Prop :=
  ∀ D : Circuit, Monotone2 D → Represents (fun u v : Fin 12 => decide (u ≠ v)) D →
    (D.gates.filter isOrGate).length ≤ 23 → C.size ≤ D.size

theorem choose_crown_minimal (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23) :
    ∃ D : Circuit, Monotone2 D ∧ Represents (fun u v : Fin 12 => decide (u ≠ v)) D ∧
      (D.gates.filter isOrGate).length ≤ 23 ∧ D.size ≤ C.size ∧ crownSizeMinimal D := by
  classical
  let P (s : ℕ) := ∃ D : Circuit, D.size = s ∧ Monotone2 D ∧
    Represents (fun u v : Fin 12 => decide (u ≠ v)) D ∧ (D.gates.filter isOrGate).length ≤ 23
  have yes : P C.size := ⟨C,rfl,hm,rep,ors⟩
  have ex : ∃ s, P s := ⟨C.size,yes⟩
  obtain ⟨D,ds,dm,dr,dor⟩ := Nat.find_spec ex
  refine ⟨D,dm,dr,dor,ds ▸ Nat.find_min' ex yes,?_⟩
  intro E em er eor
  rw [ds]
  exact Nat.find_min' ex ⟨E,rfl,em,er,eor⟩

private theorem bypass_or_count (n : ℕ) (C : Circuit) (r z : ℕ) (hr : r < C.gates.length) :
    ((bypass n C r z).gates.filter isOrGate).length ≤ (C.gates.filter isOrGate).length := by
  rw [←erase_eq_bypass n C r z hr]
  simp only [PEqualNP.CircuitMoves.eraseGate,ite_eq_left hr,List.filter_append,List.length_append]
  have map_eq (l : List Gate) :
      ((l.map (fun g : Gate => ⟨g.op,g.inputs.map (PEqualNP.CircuitMoves.eraseRedirect n r z)⟩)).filter isOrGate).length =
        (l.filter isOrGate).length := by
    induction l with
    | nil => rfl
    | cons g gs ih =>
      have hg : isOrGate (⟨g.op,g.inputs.map (PEqualNP.CircuitMoves.eraseRedirect n r z)⟩ : Gate) = isOrGate g := rfl
      cases h : isOrGate g <;> simp [hg,h,ih]
  rw [map_eq]
  have sub : List.Sublist (C.gates.drop (r+1)) (C.gates.drop r) := List.drop_sublist_drop_left _ (by omega)
  have tail := (sub.filter isOrGate).length_le
  have all := congrArg (fun gs : List Gate => (gs.filter isOrGate).length) (List.take_append_drop r C.gates)
  simp only [List.filter_append,List.length_append] at all
  omega

private theorem minimal_forbids_bypass (C : Circuit) (hm : Monotone2 C)
    (mini : crownSizeMinimal C) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (r z : ℕ) (hr : r < C.gates.length)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) (bypass 24 C r z)) : False := by
  have le := mini _ (bypass_mono hm) rep ((bypass_or_count 24 C r z hr).trans ors)
  change C.gates.length ≤ (bypass 24 C r z).gates.length at le
  rw [bypass_length] at le
  omega

theorem minimal_crown_no_earlier_copy (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (mini : crownSizeMinimal C) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (r z : ℕ) (hr : r < C.gates.length) (hz : z < 24+r)
    (same : ∀ u v : Fin 12, (C.wires (oneEach u v)).getD (24+r) false =
        (C.wires (oneEach u v)).getD z false) : False := by
  apply minimal_forbids_bypass C hm mini ors r z hr
  intro u v
  have len : (oneEach u v).length = 24 := by simp [oneEach]
  exact (bypass_eval_eq len (mono_ops hm) hr (Or.inl hz) (same u v)).trans (rep u v)

theorem minimal_crown_no_raw_copy (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (mini : crownSizeMinimal C) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (r z : ℕ) (hr : r < C.gates.length) (hz : z < 24)
    (same : ∀ u v : Fin 12, (C.wires (oneEach u v)).getD (24+r) false = (oneEach u v).getD z false) : False := by
  apply minimal_crown_no_earlier_copy C hm rep mini ors r z hr (by omega)
  intro u v
  have len : (oneEach u v).length = 24 := by simp [oneEach]
  exact (same u v).trans (val_input (C := C) len hz).symm

theorem minimal_crown_offdiag_needed (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (mini : crownSizeMinimal C) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (r : ℕ) (hr : r < C.gates.length) :
    ∃ u v : Fin 12, u ≠ v ∧ (C.wires (oneEach u v)).getD (24+r) false = true := by
  by_contra! dead
  let z := 24+C.gates.length
  apply minimal_forbids_bypass C hm mini ors r z hr
  intro u v
  have len : (oneEach u v).length = 24 := by simp [oneEach]
  have off : val C (oneEach u v) z = false := val_ge len (le_refl z)
  by_cases uv : u = v
  · have le := bypass_eval_rel (R := fun a b => b = true → a = true)
      (fun _ => id) opMono_reverse len (mono_ops hm) hr (Or.inr (le_refl z))
      (by rw [off]; simp)
    have no : C.eval (oneEach u v) = false := by simpa [uv] using rep u v
    have out := (bypass 24 C r z).eval (oneEach u v)
    cases h : (bypass 24 C r z).eval (oneEach u v) <;> simp_all
  · have eq : val C (oneEach u v) (24+r) = val C (oneEach u v) z := by
      rw [off]
      cases h : val C (oneEach u v) (24+r) with
      | false => rfl
      | true => exact False.elim (by have bad := dead u v uv; simp_all [val])
    exact (bypass_eval_eq len (mono_ops hm) hr (Or.inr (le_refl z)) eq).trans (rep u v)

end PEqualNP.Research.MissingCell
