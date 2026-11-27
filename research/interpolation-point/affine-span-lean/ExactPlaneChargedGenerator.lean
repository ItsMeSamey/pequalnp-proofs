import ExactPlaneModulusCharges
import ExactPlaneSeedWork
import ExactPlaneConstructedRows
namespace ExactPlaneChargedGenerator
open ExactPlaneFieldSampler (F)
structure Output (m : Nat) where
  rows : List (Vector F m)
  modulusCandidates : Nat
  divisions : Nat
  fieldMuls : Nat
  dotEntries : Nat
  baseTables : Nat

def run : (m R : Nat) → Output m
  | 0,_ => ⟨ExactPlaneNumericalRows.zeroRow,0,0,0,0,0⟩
  | m+1,R =>
    let r := ExactPlaneConstructedRows.exponent (m+1) R
    let ms := ExactPlaneModulusCharges.search r
    let c := ms.answer.getD (fun _=>0)
    let field := ExactPlaneSeedWork.counted (m+1) (ExactPlaneEagerField.store c)
    ⟨field.rows,ms.candidates,ms.divisions,field.multiplications,field.dots,field.tables⟩

def q (m R : Nat) := if m=0 then 0 else 2^(ExactPlaneConstructedRows.exponent m R)

theorem rows_eq (m R : Nat) : (run m R).rows=ExactPlaneConstructedRows.generate m R := by
  cases m with
  | zero => rfl
  | succ m =>
    simp only [run,ExactPlaneSeedWork.counted_eq,ExactPlaneConstructedRows.generate,
      (ExactPlaneModulusCharges.search_spec _).1,ExactPlaneIrreducibleSearch.fastConstruct]

theorem counts (m R : Nat) :
    let o := run m R
    let e := ExactPlaneConstructedRows.exponent m R
    o.modulusCandidates≤q m R ∧ o.divisions≤o.modulusCandidates*(2^(e/2+1)-2) ∧
      o.fieldMuls=q m R*m ∧ o.dotEntries=(q m R)^2*m ∧ o.baseTables=q m R ∧
      o.rows.length=if m=0 then 1 else (q m R)^2 := by
  cases m with
  | zero => simp [run,q,ExactPlaneNumericalRows.zeroRow]
  | succ m =>
    have b := ExactPlaneModulusCharges.search_spec (ExactPlaneConstructedRows.exponent (m+1) R)
    simp only [run,q,Nat.succ_ne_zero,if_false,ExactPlaneSeedWork.counted_eq,ExactPlaneEagerField.seedRows_eq,
      ExactPlaneQuotientRows.count,true_and,and_true]
    exact ⟨b.2.1,b.2.2⟩
#print axioms rows_eq
#print axioms counts
end ExactPlaneChargedGenerator
