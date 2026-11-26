import ThresholdSharedFlow
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ResidualSurplus
namespace ThresholdSharedFlow
variable {C : Circuit} {n : Nat} (L : Layout C n)
theorem cascades (U V : Id C) (uv : active L U V=true) (w : Nat) :
    on L V w=true → on L U w=true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hot
    by_cases small : w<n
    · rw [on] at hot; simp [small] at hot
    by_cases idx : w-n<C.gates.length
    · let i : Id C := ⟨w-n,idx⟩
      have eq : n+i.val=w := by dsimp [i]; omega
      rw [←eq] at hot ⊢
      change active L U i=true
      change active L V i=true at hot
      by_cases iu : i=U
      · rw [row_eq,if_pos iu]
      by_cases iv : i=V
      · rw [iv]; exact uv
      rw [row_eq,if_neg iu]
      rw [row_eq,if_neg iv] at hot
      have hl := (L.atIndex i).leftEarlier
      have hr := (L.atIndex i).rightEarlier
      rw [eq] at hl hr
      cases kind : L.op i with
      | and =>
        rw [kind] at hot
        obtain ⟨l,r⟩ : on L V (L.left i)=true ∧ on L V (L.right i)=true := by simpa using hot
        simp [ih _ hl l,ih _ hr r]
      | or =>
        rw [kind] at hot
        have lr : on L V (L.left i)=true ∨ on L V (L.right i)=true := by simpa using hot
        rcases lr with l|r
        · simp [ih _ hl l]
        · simp [ih _ hr r]
    · rw [on] at hot; simp [small,idx] at hot
theorem active_trans {U V W : Id C} (uv : active L U V=true) (vw : active L V W=true) :
    active L U W=true := cascades L U V uv _ vw
end ThresholdSharedFlow
