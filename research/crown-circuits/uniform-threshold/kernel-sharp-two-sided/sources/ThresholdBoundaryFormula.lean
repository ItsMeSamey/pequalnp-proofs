import ThresholdPhysicalFirstCut
import ReadOnceLCA

namespace ThresholdBoundaryFormula
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdLeakPins
open ThresholdEffectiveColumns ThresholdOverrideCut ResidualSurplus
variable {C : Circuit} {n k : Nat} (L : Layout C n)

abbrev Param (C : Circuit) (k : Nat) := Bool ⊕ (Fin k ⊕ Id C)
abbrev Tree (C : Circuit) (k : Nat) := ReadOnceLCA.Formula (Param C k)

noncomputable def env (O : Override C k) (s : Finset (Fin k)) : Param C k → Bool
  | .inl b => b
  | .inr (.inl z) => decide (z∈s)
  | .inr (.inr j) => eval L O s j

noncomputable def atom (x y : Fin k) : Bool ⊕ Fin k → Tree C k
  | .inl b => .param (.inl b)
  | .inr z => if z=x then .left else if z=y then .right else .param (.inr (.inl z))

def gateOp : ResidualSurplus.Op → ReadOnceLCA.Op
  | .and => .conj
  | .or => .disj

noncomputable def operand (O : Override C k) (x y : Fin k) (p : Pin C)
    (rec : ∀ j : Id C, source L p=n+j.val → Tree C k) : Tree C k := by
  classical
  exact match O p with
    | some a => atom x y a
    | none => if h : ∃ j : Id C, source L p=n+j.val then
        if boundary (n:=n) h.choose then .param (.inr (.inr h.choose))
        else rec h.choose h.choose_spec
      else .param (.inl false)

noncomputable def formula (O : Override C k) (x y : Fin k) (i : Id C) : Tree C k :=
  .gate (gateOp (L.op i))
    (operand L O x y (i,false) (fun j edge => formula O x y j))
    (operand L O x y (i,true) (fun j edge => formula O x y j))
termination_by i.val
decreasing_by all_goals
  exact feeds_later L (show feeds L _ _ from edge)

private theorem eval_operand (O : Override C k) (x y : Fin k) (s : Finset (Fin k))
    (p : Pin C) (rec : ∀ j : Id C, source L p=n+j.val → Tree C k)
    (ih : ∀ j e, (rec j e).eval (env L O s) (decide (x∈s)) (decide (y∈s))=eval L O s j) :
    (operand L O x y p rec).eval (env L O s) (decide (x∈s)) (decide (y∈s)) =
      read L O s p (fun j _ => eval L O s j) := by
  classical
  unfold operand ThresholdOverrideCut.read
  cases hp : O p with
  | some a =>
    cases a with
    | inl b => rfl
    | inr z =>
      by_cases zx : z=x <;> by_cases zy : z=y <;>
        simp_all [atom,ReadOnceLCA.Formula.eval,env,ThresholdOccurrenceEval.value]
  | none =>
    by_cases fed : ∃ j : Id C, source L p=n+j.val
    · by_cases marked : boundary (n:=n) fed.choose
      · simp [fed,marked,ReadOnceLCA.Formula.eval,env]
      · simpa [fed,marked] using ih fed.choose fed.choose_spec
    · simp [fed,ReadOnceLCA.Formula.eval,env]

theorem formula_eval (O : Override C k) (x y : Fin k) (s : Finset (Fin k)) (i : Id C) :
    (formula L O x y i).eval (env L O s) (decide (x∈s)) (decide (y∈s))=eval L O s i := by
  rw [formula, eval]
  simp only [ReadOnceLCA.Formula.eval]
  rw [eval_operand L O x y s (i,false) _ (fun j e => formula_eval O x y s j),
      eval_operand L O x y s (i,true) _ (fun j e => formula_eval O x y s j)]
  cases L.op i <;> rfl
termination_by i.val
decreasing_by all_goals
  have lt := feeds_later L (show feeds L _ _ from e)
  exact lt

end ThresholdBoundaryFormula
