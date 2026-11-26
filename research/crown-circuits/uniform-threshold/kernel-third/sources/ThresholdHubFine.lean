import ThresholdHubMissing
namespace ThresholdHubFine
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrExtraction ThresholdRegularSource
open ThresholdSimpleIncidence ThresholdSharedPartition ThresholdSharedFlow ThresholdFlowPairs
open ThresholdHubDegrees ThresholdFlowSum ThresholdHighComponents ThresholdGraphCounts T2OrPartition
open T2CubeDeletion T2SoleOrSplice T2RegularOrDelete ThresholdHubDeficits ThresholdHubMissing
noncomputable def budget (n g : Nat) : ℤ := (surplus n g)^2+7*surplus n g+14-2*(n:ℤ)

theorem regular_q {n out : Nat} {gs : List Raw} (hn : 5≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    2*(q L:ℤ)≤budget n C.size ∧ M L=q L+(hotPairs L).card := by
  intro C L
  let H := hubs C n
  let b := ∑ u∈H,(singleAt L u).card
  let p := (hotPairs L).card
  let m := (internal L).card
  let e := (missed L).card
  let d := deltaO L+deltaA L
  have simple := classified_simple (by omega : 2≤n) minim reg
  have st := ThresholdSharpEndpoint.structure_of_star ThresholdStarBypass.regular_star_boundary n hn gs out minim reg
  have pairs : p+m≤H.card.choose 2 := pair_budget L simple.1 simple.2.1 st.no_shared_raw
  have cap : m≤H.card.choose 2 := by omega
  have eqM : M L+m=H.card.choose 2 := Nat.sub_add_cancel cap
  have eqq : q L+p=M L := Nat.sub_add_cancel (by omega)
  have part : n=e+m+b := partition L
  have avoid : e≤4 := st.missed_bound
  have finance : d+H.card+2*n≤C.size+1 := by
    simpa only [d,H,deltaO,deltaA,fan_readers,ThresholdSharedFunding.extrasOr,
      ThresholdSharedFunding.extrasAnd,ThresholdSharedFunding.fan] using ThresholdSharedFunding.funding minim reg
  have orig := boundary L st.leaf_bound
  have priv : b≤3*H.card+p+H.card*d := by
    by_cases pos : H.card=0
    · have empty := Finset.card_eq_zero.mp pos
      simp [b,empty]
    · have step : H.card-1+1=H.card := by omega
      have times := congrArg (fun k => k*deltaO L) step
      change b≤3*H.card+deltaO L+p+(H.card-1)*deltaO L+H.card*deltaA L at orig
      dsimp only [d]
      rw [Nat.add_mul] at times
      rw [Nat.mul_add]
      omega
  have choose := ThresholdSharpArithmetic.twice_choose_two H.card
  refine ⟨?_,eqq.symm⟩
  apply ThresholdHubBootstrap.incomparable_deficit (h:=(H.card:ℤ)) (d:=(d:ℤ))
    (e:=(e:ℤ)) (b:=(b:ℤ)) (m:=(m:ℤ)) (P:=(p:ℤ)) (by positivity) (by positivity)
  · change (H.card:ℤ)+(d:ℤ)≤(C.size:ℤ)-2*(n:ℤ)+1; omega
  · exact_mod_cast avoid
  · exact_mod_cast part
  · exact_mod_cast priv
  · zify at eqM eqq
    linarith

theorem regular_fine {n out : Nat} {gs : List Raw} (hn : 5≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    let h : ℤ := (hubs C n).card
    let low : ℤ := ((hubs C n) \ high L).card
    let B := budget n C.size
    (∀ u∈hubs C n,(raws L u).card+(after L u).card+2*n≤C.size+3) →
    4≤h → 32*(M L:ℤ)≤h*h →
    low*h≤20*B ∧ (M L:ℤ)≤5*B ∧ (Nat.card (graph L).ConnectedComponent:ℤ)≤low+5 := by
  intro C L h low B star h4 rough
  have simple := classified_simple (by omega : 2≤n) minim reg
  have st := ThresholdSharpEndpoint.structure_of_star ThresholdStarBypass.regular_star_boundary n hn gs out minim reg
  have pairs := pair_budget L simple.1 simple.2.1 st.no_shared_raw
  have ⟨qbound,eqM⟩ := regular_q hn minim reg
  change 2*(q L:ℤ)≤B at qbound
  change M L=q L+(hotPairs L).card at eqM
  have B0 : 0≤B := by omega
  have castB : (B.toNat:ℤ)=B := Int.toNat_of_nonneg B0
  have cuts (I) (hyp : ThresholdProbeIdeals.Ideal (hotPairs L) I) :
      (ThresholdProbeIdeals.Cut (hotPairs L) I).card≤B.toNat := by
    have cap : ((ThresholdProbeIdeals.Cut (hotPairs L) I).card:ℤ)≤B :=
      ThresholdPhysicalIdeals.regular_ideal_cut hn minim reg star I hyp
    omega
  have inc := low_arc_budget L B.toNat cuts (ThresholdPhysicalIdeals.high_antichain minim reg)
  have choose := ThresholdSharpArithmetic.twice_choose_two ((hubs C n) \ high L).card
  have degree := low_deficiency L simple.1 simple.2.1 (by omega)
  change low*(h-2)≤4*(M L:ℤ) at degree
  have low0 : 0≤low := Int.natCast_nonneg _
  zify at inc eqM
  change 2*(_ : ℤ)=low*(low-1) at choose
  have missing : 2*(M L:ℤ)≤2*(q L:ℤ)+4*B+low*(low-1) := by linarith
  have init := ThresholdHubBootstrap.initiate h4 low0 rough degree
  have fine := ThresholdHubBootstrap.improve low0 init missing degree
  have mm := ThresholdHubBootstrap.refined_missing low0 init missing degree
  have comp := component_bound L simple.1
  have avoid : (missed L).card≤4 := st.missed_bound
  change Nat.card (graph L).ConnectedComponent≤1+((hubs C n) \ high L).card+(missed L).card at comp
  constructor
  · linarith
  constructor
  · linarith
  · dsimp only [low]; omega
#print axioms regular_q
#print axioms regular_fine
end ThresholdHubFine
