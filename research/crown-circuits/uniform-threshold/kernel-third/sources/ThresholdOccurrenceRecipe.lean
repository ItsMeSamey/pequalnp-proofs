import ThresholdOccurrenceDebit
import ThresholdOccurrenceEval
import ThresholdFactorNetwork
namespace ThresholdOccurrenceRecipe
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction ResidualSurplus T2OrPartition
open ThresholdLeakPins ThresholdOccurrenceEval ThresholdFactorExpr ThresholdFactorNetwork
variable {C : Circuit} {n k : Nat} (L : Layout C n) (A : Assignment C k)

noncomputable def spec (s : Finset (Fin k)) (w : Nat) : Bool :=
  if h : w-n<C.gates.length then
    let i : Id C := ⟨w-n,h⟩
    if outFixed L A i then (T2SoleOrSplice.vector s).getD 0 false else eval L A s i
  else false

def atom (q : Pin C) : Term :=
  if source L q<n then match A q with | .inl _ => .raw 0 | .inr j => .raw j.val
  else .ref (source L q)
noncomputable def recipe (i : Id C) : Term :=
  if outFixed L A i then .raw 0
  else if pinFixed L A (i,false) then atom L A (i,true)
  else if pinFixed L A (i,true) then atom L A (i,false)
  else .node (L.op i) (atom L A (i,false)) (atom L A (i,true))

private theorem projection {f g : Finset (Fin k) → Bool} (o : Op)
    (cf : Const f) (non : ¬Const (fun s => act o (f s) (g s))) (s) :
    act o (f s) (g s)=g s := by
  obtain ⟨b,h⟩ := cf
  cases o <;> cases b <;> simp_all [Const,act]

private theorem atom_live (q : Pin C) (live : pinFixed L A q=false) (s : Finset (Fin k)) :
    (atom L A q).value (fun j => (T2SoleOrSplice.vector s).getD j false) (spec L A s) = pinEval L A s q := by
  by_cases h : source L q<n
  · have eq := raw_fixed L A q h
    rw [live] at eq
    cases av : A q with
    | inl b => simp [av,fixedArg] at eq
    | inr j => simp [atom,h,av,Term.value,pinEval,value,T2SoleOrSplice.vector,List.getD_eq_getElem?_getD]
  · have lt := earlier L q
    have ilt := q.1.isLt
    let j : Id C := ⟨source L q-n,by omega⟩
    have eq : source L q=n+j.val := by dsimp [j]; omega
    have flag : outFixed L A j=false := (fixed_link L A q j eq).symm.trans live
    simp [atom,h,Term.value,pinEval,eq,spec,j.isLt,flag]

theorem correct (i : Id C) (s : Finset (Fin k)) :
    (recipe L A i).value (fun j => (T2SoleOrSplice.vector s).getD j false) (spec L A s)=
      spec L A s (n+i.val) := by
  classical
  cases fo : outFixed L A i
  · have non : ¬Const (fun t => act (L.op i) (pinEval L A t (i,false)) (pinEval L A t (i,true))) := by
      intro ⟨b,all⟩
      have yes : outFixed L A i=true := decide_eq_true (show Const _ from ⟨b,fun t => (row L A t i).trans (all t)⟩)
      simp [fo] at yes
    simp only [recipe,fo,ite_false,spec,Nat.add_sub_cancel_left,dif_pos i.isLt]
    rw [row]
    cases fl : pinFixed L A (i,false) <;> cases fr : pinFixed L A (i,true)
    · exact congrArg₂ (act (L.op i)) (atom_live L A _ fl s) (atom_live L A _ fr s)
    · have c := of_decide_eq_true fr
      have comm (x y : Bool) : act (L.op i) x y=act (L.op i) y x := by cases L.op i <;> cases x <;> cases y <;> rfl
      have non' : ¬Const (fun t => act (L.op i) (pinEval L A t (i,true)) (pinEval L A t (i,false))) := by simpa only [comm (pinEval L A _ (i,true))] using non
      exact (atom_live L A _ fl s).trans (((projection (L.op i) c non' s).symm).trans (comm _ _))
    · exact (atom_live L A _ fr s).trans (projection (L.op i) (of_decide_eq_true fl) non s).symm
    · have impossible := fixed_both L A i fl fr; simp [fo] at impossible
  · simp [recipe,fo,spec,i.isLt,Term.value]

theorem cost (i : Id C) : (recipe L A i).cost=
    ThresholdOccurrenceDebit.kept (pinFixed L A) (outFixed L A) i := by
  have z (q) : (atom L A q).cost=0 := by unfold atom; split <;> first | rfl | cases A q <;> rfl
  cases fo : outFixed L A i <;> cases fl : pinFixed L A (i,false) <;> cases fr : pinFixed L A (i,true) <;>
    simp [recipe,ThresholdOccurrenceDebit.kept,Term.cost,z,fo,fl,fr]
end ThresholdOccurrenceRecipe
