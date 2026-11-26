import ThresholdPivotInjection
import ThresholdBoundaryOccurrences

namespace ThresholdBoundaryFormula
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdLeakPins
open ThresholdEffectiveColumns ThresholdOverrideCut
variable {C : Circuit} {n k : Nat} (L : Layout C n)

theorem fixed_context (O : Override C k) (x y : Fin k) (base s : Finset (Fin k))
    (d i : Id C) (le : i≤d)
    (stable : ∀ z, z≠x → z≠y → (z∈s ↔ z∈base))
    (earlier : ∀ j : Id C,j<d → boundary (n:=n) j → eval L O base j=eval L O s j) :
    (formula L O x y i).eval (env L O base) (decide (x∈s)) (decide (y∈s))=eval L O s i := by
  classical
  have pin (b : Bool) :
      (operand L O x y (i,b) (fun j _ => formula L O x y j)).eval (env L O base)
        (decide (x∈s)) (decide (y∈s)) =
      read L O s (i,b) (fun j _ => eval L O s j) := by
    unfold operand ThresholdOverrideCut.read
    cases e : O (i,b) with
    | some a =>
      cases a with
      | inl z => rfl
      | inr z =>
        by_cases zx : z=x
        · subst z; simp [atom,ReadOnceLCA.Formula.eval,ThresholdOccurrenceEval.value]
        · by_cases zy : z=y
          · subst z; simp [atom,zx,ReadOnceLCA.Formula.eval,ThresholdOccurrenceEval.value]
          · simp [atom,zx,zy,ReadOnceLCA.Formula.eval,env,ThresholdOccurrenceEval.value,
                  stable z zx zy]
    | none =>
      by_cases fed : ∃ j : Id C, source L (i,b)=n+j.val
      · have lt := feeds_later L (show feeds L fed.choose (i,b) from fed.choose_spec)
        by_cases m : boundary (n:=n) fed.choose
        · simpa [fed,m,ReadOnceLCA.Formula.eval,env] using earlier fed.choose (lt_of_lt_of_le lt le) m
        · simpa [fed,m] using fixed_context O x y base s d fed.choose (le_trans lt.le le) stable earlier
      · simp [fed,ReadOnceLCA.Formula.eval,env]
  rw [formula,eval]
  simp only [ReadOnceLCA.Formula.eval,pin]
  cases L.op i <;> rfl
termination_by i.val
decreasing_by exact lt

end ThresholdBoundaryFormula

namespace ThresholdPivotStar
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition T2SoleOrSplice
open ThresholdPhysicalFirstCut ThresholdBoundaryFormula
variable {C : Circuit} {n k : Nat} (L : Layout C n) (D : Star C n k L) (M : LexMinimum n C)

theorem physical_pair_contexts : PairContexts L D M := by
  classical
  intro x y z ne zx zy same
  let O := patch {D.pivot,D.shared} D.privatePin
  let d := first L D M x
  refine ⟨formula L O x y d,env L O ∅,env L O {z},?_,?_,?_,?_⟩
  · exact (physical_counts L M _ D.privatePin x y ne d).1
  · exact (physical_counts L M _ D.privatePin x y ne d).2
  all_goals
    intro p q
    have fam (base : Finset (Fin k)) (bx : x∉base) (by' : y∉base) :
        (formula L O x y d).eval (env L O base) p q =
          changed L D (base ∪ bits x y p q) d := by
      have ex := fixed_context L O x y base (base ∪ bits x y p q) d d le_rfl
        (fun w wx wy => by cases p <;> cases q <;> simp [bits,wx,wy])
        (fun j lt m => (earlier_unchanged L D M d j lt m base (bits x y p q) (by
          intro w hw
          have h : w=x ∨ w=y := by
            cases p <;> cases q <;> simp_all [bits]
          rcases h with rfl|rfl
          · rfl
          · exact same.symm)).symm)
      cases p <;> cases q <;> simpa [bits,bx,by',ne,Ne.symm ne,changed,O] using ex
    first
    | simpa using fam ∅ (by simp) (by simp)
    | simpa using fam {z} (by simpa using Ne.symm zx) (by simpa using Ne.symm zy)

#print axioms physical_pair_contexts
end ThresholdPivotStar
