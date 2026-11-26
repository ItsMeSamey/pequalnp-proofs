import Research.CrownSilentColumn
import Research.CrownSilentInduced
namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

private theorem length_all_wires (gs : List Gate) (out : ℕ) (w : List Bool) :
    ((Circuit.mk gs out).wires w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change ((Circuit.mk gs out).wires (advance g w)).length = _
    rw [ih,advance_len,List.length_cons]; omega

theorem silent_gate_deleted (C : Circuit) (R : Finset (Fin 24)) :
    silentGates C R ⊆ avoidingAnds C ∅ \ avoidingAnds C (silentCopyWires C R) := by
  intro k h
  obtain ⟨can,r,hr,hit⟩ := (Finset.mem_filter.mp h).2
  have cold := chargeable_cold C k can
  have act : isAndGate C.gates[k] = true ∧ C.gates[k].inputs.length = 2 := by
    have active := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp can).1).1
    refine ⟨?_,of_decide_eq_true active.2⟩
    have hh := active.1
    cases hg : C.gates[k].op <;> simp only [isAndGate,hg] at hh ⊢ <;> contradiction
  obtain ⟨a,b,shape⟩ := List.length_eq_two.mp act.2
  have which : operand C k 0 = a ∧ operand C k 1 = b := by unfold operand; rw [shape]; exact ⟨rfl,rfl⟩
  have mem (i : ℕ) (hot : r ∈ rawSupport C i)
      (off : (C.wires (List.replicate 24 false)).getD i false = false) : i ∈ silentCopyWires C R := by
    have hm := (Finset.mem_filter.mp hot).2
    have len : (C.wires (singleInput r)).length = 24 + C.gates.length := by
      simpa [singleInput] using length_all_wires C.gates C.output (singleInput r)
    have bound : i < 24+C.gates.length := by
      by_contra! bad
      rw [getD_missing (by omega)] at hm
      contradiction
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr bound,off,r,hr,hm⟩
  apply Finset.mem_sdiff.mpr
  constructor
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Bool.and_eq_true_iff.mpr ⟨act.1,List.all_eq_true.mpr (by simp)⟩⟩
  · intro hk
    have all := (Bool.and_eq_true_iff.mp (Finset.mem_filter.mp hk).2).2
    have lhs : a ∉ silentCopyWires C R ∧ b ∉ silentCopyWires C R := by rw [shape] at all; simpa using all
    have hh := of_decide_eq_true hit
    rcases hh with ll|rr
    · exact lhs.1 (which.1 ▸ mem _ ll cold.1)
    · exact lhs.2 (which.2 ▸ mem _ rr cold.2)
end PEqualNP.Research.MissingCell
