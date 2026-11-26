import ThresholdActualColdCandidates
import ThresholdNativeRowSelection
namespace ThresholdActualCoarseLoss
open PEqualNP.CircuitLowerBounds ResidualSurplus T2OrPartition T2SoleOrSplice T2CubeDeletion T2RegularOrDelete
open ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence ThresholdSecondaryReceivers
open ThresholdActualColdCandidates ThresholdEffectiveColumns ThresholdHighComponents ThresholdSharedPartition ThresholdFanoutBudget
open ThresholdNativeRowSelection

theorem cold_count {C : Circuit} {n : Nat} (L : Layout C n) (M : LexMinimum n C)
    (R U H : Finset (Id C)) (ru : R⊆U) (rh : R⊆H) (fallback : Id C) :
    (cold L M R).card ≤ ∑ a∈U,(ThresholdWarmSimple.exceptional L M H a).card := by
  classical
  let k := fun p => Sigma.mk (β:=fun _ : Id C => Id C) (first L M R p fallback) (second L M R p fallback)
  let pool := U.sigma (ThresholdWarmSimple.exceptional L M H)
  have sub : (cold L M R).image k⊆pool := by
    intro z hz
    obtain ⟨p,mem,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨eq,_,fail,ha,hb⟩ := oriented L M fallback mem
    obtain ⟨_,x,raw,v,hv,off⟩ := fail
    exact Finset.mem_sigma.mpr ⟨ru ha,Finset.mem_filter.mpr ⟨rh hb,x,
      raw.trans (eq.trans (Finset.pair_comm _ _)),v,hv,by unfold ThresholdWarmSimple.lit; rw [off]; decide⟩⟩
  have inj : Set.InjOn k (cold L M R:Set _) := by
    intro p hp q hq eq
    have fst := congrArg (fun s : Sigma (fun _ : Id C => Id C) => s.1) eq
    have snd := congrArg (fun s : Sigma (fun _ : Id C => Id C) => s.2) eq
    exact (oriented L M fallback hp).1.trans ((congrArg₂ (fun a b : Id C => ({a,b} : Finset _)) fst snd).trans
      (oriented L M fallback hq).1.symm)
  have cap := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn inj] at cap
  simpa [pool,Finset.card_sigma] using cap

theorem native {n out : Nat} {gs : List Raw} (hn : 2≤n) (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (R : Finset (Id (source gs out))) (fallback : Id (source gs out))
    (boxes : Finset (Finset (Id (source gs out)))) (four : ∀ F∈boxes,F.card=4) :
    let L := layout n gs out M.eligible
    let H := high L
    R⊆retained L → R⊆H →
    ∑ F∈boxes, ((ThresholdEffectiveMatchingRows.fiber R (effective L M) F).card-1) ≤
      (missing L H).card+2*H.card*((hubs (source gs out) n) \ H).card := by
  classical
  intro L H sub inH
  let pool := competing L M R
  let miss := missing L R
  let bad := cold L M R
  have b := ThresholdColdMatchingLoss.loss_le_exceptions boxes pool miss bad (box L M)
    (fun F _ _ => ThresholdHotMatching.fiber_unique hn M reg pool miss bad (box L M)
      (fun _ mem => actual_hot L M mem)
      (fun p _ r hr v hv => Finset.mem_biUnion.mpr ⟨r,hr,hv⟩) F)
  have sumEq : (∑ F∈boxes, ((ThresholdColdMatchingLoss.fiber (competing L M R) (box L M) F).card-1)) =
      ∑ F∈boxes, ((ThresholdEffectiveMatchingRows.fiber R (effective L M) F).card-1) :=
    Finset.sum_congr rfl (fun F mem => box_deficiency L M (four F mem))
  change (∑ F∈boxes, ((ThresholdColdMatchingLoss.fiber (competing L M R) (box L M) F).card-1)) ≤ _ at b
  rw [sumEq] at b
  exact b.trans (Nat.add_le_add (Finset.card_le_card (missing_mono L inH))
    ((cold_count L M R (retained L) H sub inH fallback).trans (cold_before_deletion hn M reg)))

#print axioms native
end ThresholdActualCoarseLoss
