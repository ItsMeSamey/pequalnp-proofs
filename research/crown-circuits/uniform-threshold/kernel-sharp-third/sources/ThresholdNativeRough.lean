import ThresholdNativeCoarse
import ThresholdHubPrefixNative
namespace ThresholdNativeRough
open PEqualNP.CircuitLowerBounds ResidualSurplus T2CubeDeletion T2SoleOrSplice
open T2RegularOrDelete ThresholdSharedPartition ThresholdRegularSource ThresholdHubMissing
open ThresholdFlowPairs ThresholdHubFine

theorem rough {n out : Nat} {gs : List Raw} (hn : 5≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs) (t E : ℝ)
    (sq : t^2=2*(n:ℝ)) (cut : (2:ℝ)^200≤t)
    (ex : E=1+max 0 (((source gs out).size:ℝ)-2*(n:ℝ)-t))
    (small : E^5≤t^3) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    let h : ℤ := (hubs C n).card
    32*(M L:ℤ)≤h*h := by
  intro C L h
  let H := (hubs C n).card
  let Z := ThresholdHubFine.budget n C.size
  have zn : (Z:ℝ)=((C.size:ℝ)-2*(n:ℝ))^2+7*((C.size:ℝ)-2*(n:ℝ))+14-t^2 := by
    dsimp [Z,ThresholdHubFine.budget,ThresholdHubDeficits.surplus]
    push_cast
    rw [sq]
  obtain ⟨_,_,_,th,_,bound,h4⟩ := ThresholdNativeCoarse.parameters hn minim reg t E sq cut ex small
  have th' : t≤2*(H:ℝ) := th
  have zbound : (Z:ℝ)≤12*t*E := zn.trans_le bound
  obtain ⟨qle,split⟩ := regular_q hn minim reg
  change 2*(q L:ℤ)≤Z at qle
  change M L=q L+(hotPairs L).card at split
  have zpos : 0≤Z := by omega
  have e1 : 1≤E := by rw [ex]; linarith [le_max_left 0 ((C.size:ℝ)-2*(n:ℝ)-t)]
  have qreal : 2*(q L:ℝ)≤(Z:ℝ) := by exact_mod_cast qle
  obtain ⟨zc,qc⟩ := ThresholdCoarseDensity.budgets (by linarith : 0≤t)
    (by positivity : 0≤(H:ℝ)) e1 (ThresholdCoarseDensity.small_ratio cut small)
    th' zbound (by linarith [show 0≤(H:ℝ) by positivity] : (Z:ℝ)≤Z+3*(H:ℝ)) qreal
  have hlarge : 256≤H := by
    have hr : (256:ℝ)≤H := by linarith only [th',cut]
    exact_mod_cast hr
  obtain ⟨d1,d2⟩ := ThresholdCoarseDensity.divisor H hlarge
  have sN := ThresholdHubPrefixNative.regular_prefix hn minim reg (H/128)
  change (hotPairs L).card*(H/128)≤H*(H/128)^2+H*Z.toNat at sN
  have znat : (Z.toNat:ℝ)=(Z:ℝ) := by exact_mod_cast Int.toNat_of_nonneg zpos
  have sand : ((hotPairs L).card:ℝ)*((H/128:Nat):ℝ)≤
      (H:ℝ)*((H/128:Nat):ℝ)^2+(H:ℝ)*(Z:ℝ) := by
    rw [←znat]
    exact_mod_cast sN
  have out := ThresholdCoarseDensity.coarse (show 0<(H:ℝ) by exact_mod_cast (by omega : 0<H))
    (by exact_mod_cast d1) (by exact_mod_cast d2) (by positivity) sand zc qc
    (show (M L:ℝ)=(q L:ℝ)+((hotPairs L).card:ℝ) by exact_mod_cast split)
  change 32*(M L:ℤ)≤(H:ℤ)*H
  rw [pow_two] at out
  exact_mod_cast out
end ThresholdNativeRough
