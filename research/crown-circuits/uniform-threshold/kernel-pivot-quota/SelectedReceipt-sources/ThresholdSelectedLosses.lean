import ThresholdSupportBoxes
import ThresholdActualCoarseLoss
import ThresholdHighMissingIdentity
import ThresholdNativeSharpColumnLedger
import Batteries.Tactic.OpenPrivate
namespace ThresholdNativeRowSelection
open PEqualNP.CircuitLowerBounds T2SoleOrSplice T2RegularOrDelete T2CubeDeletion ResidualSurplus
open T2OrPartition ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence ThresholdSharedPartition
open ThresholdEffectiveColumns ThresholdSecondaryReceivers ThresholdHighComponents ThresholdAmbientEffectiveGraph
open private has_shared from ThresholdNativeRowSelection
open scoped BigOperators
theorem both_losses {n out : Nat} {gs : List Raw} (hn : 2≤n) (minim : LexMinimum n (source gs out))
    (reg : Regular n gs) (R : Finset (Id (source gs out)))
    (sub : R⊆retained (layout n gs out minim.eligible))
    (two : ∀ r∈R,(effective (layout n gs out minim.eligible) minim r).card=2)
    (inj : Set.InjOn (effective (layout n gs out minim.eligible) minim) (R:Set _)) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    let col := effective L minim
    let H := high L
    let W := support R col
    let loss := ∑ X : Four W,((ThresholdEffectiveMatchingRows.fiber R col (ambientBox W X)).card-1)
    loss≤(ThresholdNativeColumnCharge.inner L H).card+2*H.card*((hubs C n) \ H).card ∧
    loss≤(ThresholdNativeColumnCharge.inner L H).card+2*∑ v : ↥W,(activeGraph R col).degree v^2 := by
  classical
  intro C L col H W loss
  obtain ⟨_,_,fallback,_⟩ := regular_inputs n gs out minim.eligible reg
  have hh : H⊆hubs C n := Finset.filter_subset _ _
  have good (r) (hr : r∈retained L) := (good_pure L (Finset.mem_sdiff.mp hr).1).1
  have pure (r) (hr : r∈retained L) := (good_pure L (Finset.mem_sdiff.mp hr).1).2
  have rh : R⊆H := fun r hr => (Finset.mem_filter.mp (good r (sub hr))).1
  let shared (r : Id C) := if h : r∈R then (has_shared L r (sub h)).choose else fallback
  have sharedSpec (r) (hr : r∈R) : shared r∈signature C n r ∧ shared r∈hubs C n := by
    simpa [shared,hr] using (has_shared L r (sub hr)).choose_spec
  have outside (r) (hr : r∈R) : shared r∉H := by
    have e := receiver_later L (good r (sub hr)) (sharedSpec r hr).1
    intro stop
    exact ThresholdPhysicalIdeals.high_antichain minim reg r (rh hr) _ stop
      ((ThresholdPhysicalIdeals.mem_pair L r _).mpr ⟨⟨hh (rh hr),(sharedSpec r hr).2⟩,e.1.ne,e.2⟩)
  have tag (r) (hr : r∈R) : ∃ P,P≠shared r ∧ signature C n r={shared r,P} ∧
      2≤(readers C (n+(shared r).val)).length := by
    have ⟨member,sh⟩ := sharedSpec r hr
    obtain ⟨a,b,ne,eq⟩ := Finset.card_eq_two.mp (signature_two L (regular_inputs n gs out minim.eligible reg).1
      minim hn H hh r (good r (sub hr)))
    have share := (List.mem_filter.mp (List.mem_toFinset.mp sh)).1
    have num : 2≤(readers C (n+(shared r).val)).length := by simpa using (List.mem_filter.mp share).2
    rw [eq] at member
    rcases Finset.mem_insert.mp member with e|e
    · exact ⟨b,by simpa [e] using ne.symm,by simpa [e] using eq,num⟩
    · have z := Finset.mem_singleton.mp e
      exact ⟨a,by simpa [z] using ne,by simpa [z] using eq.trans (Finset.pair_comm _ _),num⟩
  obtain ⟨ej,inc,adj⟩ := edge_suite R col fallback two inj
  have coarse := ThresholdActualCoarseLoss.native hn minim reg R fallback (boxes W) (box_four W) sub rh
  have fine := ThresholdActualFineLoss.native hn minim reg R (retained L) H sub rh good pure
    (fullGraph R col) (edge col fallback) shared outside tag fallback (boxes W) (box_four W) inj two ej inc adj
  let f := fun X => (ThresholdEffectiveMatchingRows.fiber R col X).card-1
  have eq : (∑ X∈boxes W,f X)=loss := sum_boxes W f
  change (∑ X∈boxes W,f X)≤_ at coarse fine
  rw [eq] at coarse fine
  rw [degree_square R col] at fine
  have same : ThresholdActualColdCandidates.missing L H=ThresholdNativeColumnCharge.inner L H :=
    ThresholdHighMissingIdentity.native minim reg
  rw [same] at coarse fine
  exact ⟨coarse,fine⟩
end ThresholdNativeRowSelection
