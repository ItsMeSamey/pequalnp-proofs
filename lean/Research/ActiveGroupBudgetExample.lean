import Research.ActiveGroupBudget

open scoped BigOperators Classical

namespace LayoutActive.BudgetExample

private def measure : Bool → Unit → ℚ →ₗ[ℚ] ℚ
  | false, _ => 0
  | true, _ => LinearMap.id

private def point : Bool → ℚ
  | false => 1
  | true => 2

private def mismatch (_ : Bool) (_ : Unit) : Prop := True

private theorem active : measure true () ≠ 0 := by
  intro h
  have h' := LinearMap.congr_fun h (1 : ℚ)
  simp [measure] at h'

/-- Both samples mismatch. The inactive one evaluates at the unique root of
1 − X. The other uses the identity measurement. Both budget terms are tight. -/
example :
    let T : Finset Bool := {false, true}
    let V : Finset Unit := {()}
    let G : Finset Unit := {()}
    (∑ v ∈ V, (T.filter (fun t => mismatch t v)).card) ≤ V.card * 1 +
      ∑ t ∈ T, 1 * (G.filter (fun g => measured (measure t g))).card ∧
    (∑ v ∈ V, (T.filter (fun t => mismatch t v)).card) =
      V.card * 1 + ∑ t ∈ T, 1 * (G.filter (fun g => measured (measure t g))).card := by
  classical
  dsimp only
  constructor
  · have bound := polynomial_layout_budget (K := ℚ) {false, true} {()} {()}
      (fun _ _ => ℚ) (fun _ _ => ℚ) measure (fun _ _ => ())
      mismatch (fun _ => 1) 1 point
      (by intro t ht u hu h; cases t <;> cases u <;> norm_num [point] at *)
      (fun _ => 1 - Polynomial.X) (by simp)
      (by intro v hv; exact (Polynomial.natDegree_sub_le _ _).trans (by simp))
      (fun t _ => measure t ()) (fun t _ => if t then -1 else 1)
      (by simp) (by simp)
      (by intro t ht v hv h; cases t <;> norm_num [measure, point])
      (fun _ _ _ _ _ => le_rfl)
    exact bound
  · have allMismatch (v : Unit) :
        ({false, true} : Finset Bool).filter (fun t => mismatch t v) = {false, true} :=
      Finset.filter_eq_self.mpr (fun _ _ => trivial)
    simp [allMismatch, measured, measure, show (LinearMap.id : ℚ →ₗ[ℚ] ℚ) ≠ 0 from active]

end LayoutActive.BudgetExample
