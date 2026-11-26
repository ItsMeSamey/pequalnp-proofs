import ThresholdOccurrenceCompiler
import ThresholdSlotTruth
import ThresholdHubDegrees
import ThresholdDegreeBudget
namespace ThresholdNativeStarSaving
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ResidualSurplus T2OrPartition
open T2SoleOrSplice T2RegularOrDelete T2CubeDeletion ThresholdOrExtraction ThresholdRegularSource
open ThresholdStarRawSlots ThresholdSharedPartition ThresholdSharedOrBudget ThresholdSharedFlow
open ThresholdOccurrenceEval ThresholdOccurrenceDebit
theorem trace {C : Circuit} {n k} (L : Layout C n) (u : Id C) (x : Fin n)
    (e : ↥(star L u) ≃ Fin k) (s : Finset (Fin k)) :
    let A := choice L u x e
    ThresholdSlotEvaluation.Trace L (fun i b => input L u x e (fun j => decide (j∈s)) (i,b))
      (wire L A s) := by
  intro A
  constructor
  intro i
  rw [wire_gate,row]
  have pin (b : Bool) : value (A (i,b)) s=input L u x e (fun j => decide (j∈s)) (i,b) := by
    unfold input; change value (A _) _=(A _).elim _ _
    cases A (i,b) <;> rfl
  simp only [pinEval,ThresholdSlotEvaluation.read,pin]
  rfl

theorem star_saving {n out : Nat} {gs : List Raw} (hn : 2≤n)
    (M : LexMinimum n (source gs out)) (reg : Regular n gs)
    (u : Id (source gs out)) (hu : u∈hubs (source gs out) n) :
    let L := layout n gs out M.eligible
    let k := (ThresholdHubDegrees.raws L u).card
    let t := (ThresholdHubDegrees.after L u).card
    2≤k → ∃ D : Circuit, Monotone2 D ∧ Computes k D ∧
      D.size+(2*n-k)+t+1≤(source gs out).size := by
  classical
  intro L k t hk
  let C := source gs out
  let e : ↥(star L u) ≃ Fin k := (star L u).equivFin
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<(star L u).card by change 0<k;omega)
  let A := choice L u x e
  obtain ⟨internal,twice,j,obs⟩ := regular_inputs n gs out M.eligible reg
  have hubMem (a : Id C) (h : a∈hubs C n) : a∈sharedGates C n :=
    (List.mem_filter.mp (List.mem_toFinset.mp h)).1
  have stop := shared_stops (hubMem u hu)
  have truth (s : Finset (Fin k)) : eval L A s j=true ↔ 2≤s.card := by
    have h := ThresholdSlotEvaluation.truth M reg u x hx e s (wire L A s) (trace L u x e s) stop
    change C.output=n+j.val at obs
    change wire L A s C.output=true ↔ _ at h
    simpa only [obs,wire_gate] using h
  have notFixed : outFixed L A j=false := by
    apply decide_eq_false
    rintro ⟨b,h⟩
    have hi := (truth Finset.univ).mpr (by simpa using hk)
    have lo : eval L A ∅ j≠true := fun yes => by simpa using (truth ∅).mp yes
    change ∀ s, eval L A s j=b at h
    rw [h] at hi lo
    exact lo hi
  let H := insert u (ThresholdHubDegrees.after L u)
  have paid (a : Id C) (ha : a∈H) : outFixed L A a=true ∧ 2≤fan L a := by
    have data : a=u ∨ (a∈hubs C n ∧ u≠a ∧ active L u a=true) := by
      simpa [H,ThresholdHubDegrees.after] using ha
    have hub : a∈hubs C n := data.elim (fun eq => eq ▸ hu) (fun h => h.1)
    refine ⟨?_,?_⟩
    · apply decide_eq_true
      refine ⟨true,fun s => ?_⟩
      have tr := trace L u x e s
      have hot := ThresholdSlotEvaluation.center_hot L u x hx e _ _ tr internal stop
      rcases data with eq | h
      · subst a; simpa [wire_gate] using hot
      · simpa only [wire_gate] using ThresholdSlotEvaluation.probe_lower L tr u hot a h.2.2
    · rw [fan_readers]
      simpa [sharedGates] using hubMem a hub
  obtain ⟨D,dm,price,agree⟩ := ThresholdOccurrenceCompiler.compile_saving L A (by omega) j obs notFixed M H paid
  have rawPrice : rawFixed L (pinFixed L A)=2*n-k := by
    rw [←fixed_card L u x e internal hn M stop (fun y => twice y y.isLt)]
    unfold rawFixed fixedPins
    congr 1
    ext p
    by_cases h : ThresholdLeakPins.source L p<n
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and,h,raw_fixed L A p h]
      change fixedArg (A p)=true ↔ (A p).isLeft=true
      cases A p <;> rfl
    · simp [h]
  have hH : H.card=t+1 := Finset.card_insert_of_notMem (by simp [ThresholdHubDegrees.after])
  rw [rawPrice,hH] at price
  refine ⟨D,dm,fun s => by rw [agree]; exact truth s,by omega⟩

#print axioms star_saving
end ThresholdNativeStarSaving
