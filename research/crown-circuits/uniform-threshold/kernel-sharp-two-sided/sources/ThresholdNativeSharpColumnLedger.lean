import ThresholdFinalCoreCharge
import ThresholdAllPrivateBudget
namespace ThresholdNativeRowSelection
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2RegularOrDelete T2CubeDeletion
open T2OrPartition ThresholdOrExtraction ThresholdRegularSource ThresholdSharedPartition ThresholdHighComponents
open ThresholdEffectiveColumns ThresholdSecondaryReceivers ThresholdWarmSimple ThresholdPurityPins
open ThresholdFanoutBudget ThresholdFlowSum ThresholdSharedFlow ThresholdNativeColumnCharge

theorem selected_columns {n out : Nat} {gs : List Raw} (hn : 5≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs)
    (room : let L := layout n gs out minim.eligible
      9*trimCost L < (high L).card^2)
    (space : let L := layout n gs out minim.eligible
      let h := hubs (source gs out) n
      2*((h \ high L).card+2*(trimCost L).sqrt+1)≤h.card) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    let H := high L
    let h := hubs C n
    let m := (trimCost L).sqrt
    let d := h.card-((h \ H).card+4*m)
    ∃ G⊆retained L,∃ t,
      ThresholdColumnPeel.MinTwo (fun v r => v∈effective L minim r) G ∧
      (∀ a∈G,(effective L minim a).card=2) ∧ Set.InjOn (effective L minim) (G : Set _) ∧
      (∀ a∈G,a∈good C n H ∧ (makeBlock L Fin.val a).exts=[] ∧
        (missing L H a).card≤m ∧ (exceptional L minim H a).card≤m) ∧
      H.card≤G.card+(impure L H).card+deltaO L+3*(andIds C).length+
        4*t+m+2*(receivers C n H).card ∧ t.choose 2≤ThresholdHubMissing.M L+1 ∧
      2*((d:ℤ)*((G.biUnion (effective L minim)).card:ℤ)+((inner L H).card:ℤ))≤
        ThresholdHubFine.budget n C.size := by
  intro C L H h m d
  obtain ⟨K,kr,G,gk,_,core,two,inj,perRow,price⟩ := regular_selected hn minim reg room
  obtain ⟨t,ap,choose⟩ := ThresholdAllPrivateBudget.native (by omega : 2≤n) minim reg
  let low := (h \ H).card
  have pos : 2*(low+2*m+1)≤h.card := space
  have sq : m*m≤trimCost L := Nat.sqrt_le _
  have ordinal : 9*trimCost L<H.card^2 := room
  have enough : m+m<H.card := by
    by_contra! bad
    have ut := Nat.mul_le_mul bad bad
    nlinarith
  change H.card≤G.card+(impure L H).card+deltaO L+2*(andIds C).length+(allPrivate L).card+m+
    2*(receivers C n H).card at price
  change (allPrivate L).card≤(andIds C).length+4*t at ap
  refine ⟨G,gk.trans kr,t,core,two,inj,perRow,by omega,choose,?_⟩
  exact ThresholdFinalCoreCharge.final_core minim reg hn G m m d (low+4*m)
    (fun r hr=>(perRow r hr).1) core two (fun r hr=>(perRow r hr).2.2.1)
    (fun r hr=>(perRow r hr).2.2.2) (by change 2*(low+m+m+1)≤h.card; omega) enough
    (by change (h.card-(low+4*m))+(low+4*m)=h.card; omega) (by change low+2*m+2*m≤low+4*m; omega)
end ThresholdNativeRowSelection
