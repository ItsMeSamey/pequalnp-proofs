import Research.FalseOrCount

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- A list indexed chronologically by the gate position. Entry k is true exactly when
gate k is an OR whose output on the specified starting wires is true. -/
def trueOrFlags : List Gate → List Bool → List Bool
  | [], _ => []
  | g :: gs, w =>
    (isOrGate g && g.op.eval (g.inputs.map fun i => w.getD i false)) ::
      trueOrFlags gs (advance g w)

def allOrFalse : List Gate → List Bool → Prop
  | [], _ => True
  | g :: gs, w => (isOrGate g = true → g.op.eval (g.inputs.map fun i => w.getD i false) = false) ∧
      allOrFalse gs (advance g w)

theorem trueOrFlags_length (gs : List Gate) (w : List Bool) :
    (trueOrFlags gs w).length = gs.length := by
  induction gs generalizing w <;> simp_all [trueOrFlags]

theorem trueOrFlags_balance (gs : List Gate) (w : List Bool) :
    (trueOrFlags gs w).count true + falseOrCount gs w = (gs.filter isOrGate).length := by
  induction gs generalizing w with
  | nil => simp [trueOrFlags,falseOrCount]
  | cons g gs ih =>
    have ht := ih (advance g w)
    cases ho : isOrGate g <;> cases he : g.op.eval (g.inputs.map fun i => w.getD i false) <;>
      simp only [trueOrFlags,falseOrCount,ho,he,Bool.false_and,Bool.true_and,Bool.not_true,
        Bool.not_false,List.count_cons,List.filter_cons,↓reduceIte,Bool.false_eq_true,
        List.length_cons] <;> simp <;> omega

theorem trueOrFlags_zero (gs : List Gate) (w : List Bool)
    (h : (trueOrFlags gs w).count true = 0) : allOrFalse gs w := by
  induction gs generalizing w with
  | nil => trivial
  | cons g gs ih =>
    change _ ∧ _
    have hn : true ∉ trueOrFlags (g :: gs) w := List.count_eq_zero.mp h
    change true ∉ _ :: trueOrFlags gs (advance g w) at hn
    have hhn := List.ne_and_not_mem_of_not_mem_cons hn
    refine ⟨?_, ih (advance g w) (List.count_eq_zero.mpr hhn.2)⟩
    intro ho
    cases he : g.op.eval (g.inputs.map fun i => w.getD i false)
    · rfl
    · exact False.elim (hhn.1 (by simp only [ho,he,Bool.and_self]))

theorem crown_trueOrFlags_le (i : Fin 12) (C : Circuit) (hm : Monotone2 C)
    (hr : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) :
    (trueOrFlags C.gates (oneEach i i)).count true ≤ (C.gates.filter isOrGate).length - 21 := by
  have := crown_twelve_falseOrCount i C hm hr
  have := trueOrFlags_balance C.gates (oneEach i i)
  omega

theorem crown_all_ors_false (i : Fin 12) (C : Circuit) (hm : Monotone2 C)
    (hr : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (hc : (C.gates.filter isOrGate).length ≤ 21) : allOrFalse C.gates (oneEach i i) := by
  apply trueOrFlags_zero
  have := crown_trueOrFlags_le i C hm hr
  omega

theorem crown_at_most_one_true_or (i : Fin 12) (C : Circuit) (hm : Monotone2 C)
    (hr : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (hc : (C.gates.filter isOrGate).length ≤ 22) :
    (trueOrFlags C.gates (oneEach i i)).count true ≤ 1 := by
  have := crown_trueOrFlags_le i C hm hr
  omega

end PEqualNP.Research.MissingCell
