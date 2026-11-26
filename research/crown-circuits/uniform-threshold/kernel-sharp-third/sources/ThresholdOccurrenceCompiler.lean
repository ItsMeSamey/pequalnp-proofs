import ThresholdOccurrenceRecipe
import ThresholdFlowFanout
namespace ThresholdOccurrenceCompiler
open ThresholdOrGroups PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ResidualSurplus ThresholdOrExtraction T2OrPartition
open ThresholdLeakPins ThresholdOccurrenceEval ThresholdOccurrenceRecipe ThresholdFactorExpr ThresholdFactorNetwork
open ThresholdOccurrenceDebit T2SoleOrSplice
variable {C : Circuit} {n k : Nat} (L : Layout C n) (A : Assignment C k)

private theorem ready {j : Id C} (hk : 0<k) (seen : List Nat)
    (prev : ∀ i : Id C,i<j → n+i.val∈seen) : (recipe L A j).Avail k seen := by
  have port (b : Bool) : (atom L A (j,b)).Avail k seen := by
    unfold atom
    split
    · cases A (j,b) with
      | inl _ => exact hk
      | inr v => exact v.isLt
    · rename_i raw
      have bound := earlier L (j,b)
      change source L (j,b)<n+j.val at bound
      let i : Id C := ⟨source L (j,b)-n,by have := j.isLt; omega⟩
      have lt : i<j := by change source L (j,b)-n < j.val; omega
      have eq : n+i.val=source L (j,b) := by dsimp [i]; omega
      exact eq ▸ prev i lt
  unfold recipe
  split
  · exact hk
  split
  · exact port true
  split
  · exact port false
  exact ⟨port false,port true⟩

theorem compile (hk : 0<k) (out : Id C) (non : outFixed L A out=false) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size=(∑ i : Id C,kept (pinFixed L A) (outFixed L A) i) ∧
      ∀ s : Finset (Fin k),D.eval (vector s)=eval L A s out := by
  classical
  let price := kept (pinFixed L A) (outFixed L A)
  let S := spec L A
  have buildBefore (t : Nat) (ht : t≤C.gates.length) :
      ∃ seen : List Nat, ∃ W : Work k vector S seen,
      (∀ i : Id C,i.val<t → n+i.val∈seen) ∧
      W.gs.length=∑ i : Id C,if i.val<t then price i else 0 := by
    induction t with
    | zero =>
      let W : Work k vector S [] := ⟨[],id,by simp [Mono],by simp,by simp⟩
      exact ⟨[],W,by simp,by simp [W]⟩
    | succ t ih =>
      obtain ⟨seen,W,prev,old⟩ := ih (by omega)
      let j : Id C := ⟨t,by omega⟩
      let J : Job := ⟨n+j.val,recipe L A j⟩
      have ok : valid k seen [J] := ⟨ready L A hk seen prev,trivial⟩
      obtain ⟨F,sz⟩ := program (fun s : Finset (Fin k) => by simp [vector]) [J] seen W ok (by
        intro a ha s
        have eq : a=J := by simpa using ha
        subst a
        exact correct L A j s)
      refine ⟨J.output::seen,F,?_,?_⟩
      · intro i hi
        by_cases eq : i=j
        · simp [eq,J]
        · have ne : i.val≠t := fun h => eq (Fin.ext h)
          exact List.mem_cons_of_mem _ (prev i (by omega))
      · have split (i : Id C) : (if i.val<t+1 then price i else 0)=
            (if i.val<t then price i else 0)+(if i=j then price j else 0) := by
          by_cases eq : i=j
          · simp [eq,j]
          · have ne : i.val≠t := fun h => eq (Fin.ext h)
            by_cases lt : i.val<t <;> simp [eq,lt,show (i.val<t+1) ↔ i.val<t by omega]
        simp only [split,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
        simpa [J,price,old,cost] using sz
  obtain ⟨seen,W,prev,sz⟩ := buildBefore C.gates.length le_rfl
  refine ⟨⟨W.gs,W.ren (n+out.val)⟩,fun g h => ⟨(W.mono g h).1,(W.mono g h).2.le⟩,?_,?_⟩
  · change W.gs.length = _
    simpa [price,Fin.isLt] using sz
  · intro s
    have h := W.correct _ (prev out out.isLt) s
    change (run W.gs (vector s)).getD (W.ren (n+out.val)) false=_
    simpa [S,spec,out.isLt,non] using h

theorem compile_saving (hk : 0<k) (out : Id C) (obs : C.output=n+out.val)
    (non : outFixed L A out=false) (mini : LexMinimum n C)
    (H : Finset (Id C)) (shared : ∀ i∈H, outFixed L A i=true ∧ 2≤ThresholdSharedFlow.fan L i) :
    ∃ D : Circuit, Monotone2 D ∧ D.size+rawFixed L (pinFixed L A)+H.card≤C.size ∧
      ∀ s : Finset (Fin k),D.eval (vector s)=eval L A s out := by
  obtain ⟨D,dm,cost,ok⟩ := compile L A hk out non
  have live (i : Id C) (hi : outFixed L A i=true) : 1≤ThresholdSharedFlow.fan L i := by
    rw [ThresholdSharedFlow.fan_readers]
    apply ThresholdFanoutBudget.live_slots L mini
    intro eq
    have same : i=out := Fin.ext (by omega)
    simp [same,non] at hi
  have price := telescope L (pinFixed L A) (outFixed L A) H (fixed_link L A) (fixed_both L A) live shared
  exact ⟨D,dm,by rw [cost]; exact price,ok⟩
#print axioms compile_saving
end ThresholdOccurrenceCompiler
