import ThresholdReceiverScale
import ThresholdReceiverAndBudget
import ThresholdGoodCount
import ThresholdHubFine
import ThresholdCoarseDensity
namespace ThresholdReceiverWindow
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrExtraction ThresholdRegularSource
open ThresholdSimpleIncidence ThresholdSharedPartition ThresholdHubDegrees ThresholdHighComponents
open ThresholdFlowSum ThresholdSharedFlow ThresholdSecondaryReceivers ThresholdFanoutBudget
open T2SoleOrSplice T2CubeDeletion T2RegularOrDelete
theorem window {n out : Nat} {gs : List Raw} (hn : 5≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs) (t E : ℝ) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    let H := high L
    let h : ℝ := (hubs C n).card
    let l : ℝ := ((hubs C n) \ H).card
    let g : ℝ := (good C n H).card
    let w : ℝ := (receivers C n H).card
    let d : ℝ := C.size-2*(n:ℝ)+1-h
    (2:ℝ)^200≤t → 1≤E → E^5≤t^3 → t^2=2*(n:ℝ) → (C.size:ℝ)-2*n≤t+E →
    t≤2*h → 1≤h → d^2≤32*t*E → l≤730*E → (ThresholdHubMissing.M L:ℝ)≤180*h*E →
    h≤2*g ∧ w≤3000*E ∧ w^3≤g^2 := by
  classical
  intro C L H h l g w d cut one small sq exc th big dsq low miss
  let a : ℝ := (andIds C).length
  let m : ℝ := (internal L).card
  let e : ℝ := (missed L).card
  let c : ℝ := Nat.card (graph L).ConnectedComponent
  let s : ℝ := (C.size:ℝ)-2*n
  let mss : ℝ := ThresholdHubMissing.M L
  have geom := ThresholdSharpEndpoint.structure_of_star ThresholdStarBypass.regular_star_boundary n hn gs out minim reg
  have pair := ThresholdFlowPairs.pair_budget L (classified_simple (by omega) minim reg).1
    (classified_simple (by omega) minim reg).2.1 geom.no_shared_raw
  have fund : deltaO L+deltaA L+(hubs C n).card+2*n≤C.size+1 := by
    simpa only [deltaO,deltaA,fan_readers,ThresholdSharedFunding.extrasOr,
      ThresholdSharedFunding.extrasAnd,ThresholdSharedFunding.fan] using ThresholdSharedFunding.funding minim reg
  have rawN : ThresholdHubMissing.M L+(internal L).card=(hubs C n).card.choose 2 :=
    Nat.sub_add_cancel (by omega)
  have twon := ThresholdSharpArithmetic.twice_choose_two (hubs C n).card
  have raw : 2*(m+mss)=h*(h-1) := by
    have t' : 2*((hubs C n).card.choose 2:ℝ)=h*(h-1) := by
      dsimp only [h]
      have tmp := congrArg (fun z : ℤ => (z:ℝ)) twon
      push_cast at tmp
      exact tmp
    have r' : mss+m=((hubs C n).card.choose 2:ℝ) := by dsimp only [mss,m]; exact_mod_cast rawN
    linarith
  have sumN := ThresholdReceiverAndBudget.physical (by omega) minim reg
  have sumR : (n:ℝ)+m+h*(a+2*(n:ℝ)) ≤ e+h*((C.size:ℝ)+4+c) := by
    dsimp only [m,h,a,e,c]
    dsimp only at sumN
    exact_mod_cast sumN
  have sum : (n:ℝ)+m+h*a≤e+h*(s+4+c) := by dsimp [s]; nlinarith only [sumR]
  have av : e≤4 := by dsimp only [e]; exact_mod_cast geom.missed_bound
  have comp : c≤1+l+e := by
    dsimp only [c,l,e,H]
    exact_mod_cast ThresholdHighComponents.component_bound L (classified_simple (by omega) minim reg).1
  have ands : a≤930*E := ThresholdReceiverAndBudget.count_real t n s h e m mss c a l E one big sq exc sum raw av low comp miss
  have sub : H⊆hubs C n := Finset.filter_subset _ _
  have anti (u) (hu : u∈H) (v) (hv : v∈H) (ne : u≠v) : active L u v=false := by
    have no := ThresholdPhysicalIdeals.high_antichain minim reg u hu v hv
    cases on : active L u v
    · rfl
    · exact False.elim (no ((ThresholdPhysicalIdeals.mem_pair L u v).mpr ⟨⟨sub hu,sub hv⟩,ne,on⟩))
  have wbound : w≤l+2*a+1 := by dsimp only [w,l,a]; exact_mod_cast receiver_budget L minim H anti
  have gb : (H.card:ℝ)≤g+(deltaO L:ℝ)+2*a := by dsimp only [g,a]; exact_mod_cast good_count L H sub
  have split : l+(H.card:ℝ)=h := by dsimp only [l,h]; exact_mod_cast Finset.card_sdiff_add_card_eq_card sub
  have spent : (deltaO L:ℝ)+(deltaA L:ℝ)+h+2*(n:ℝ)≤(C.size:ℝ)+1 := by dsimp only [h]; exact_mod_cast fund
  have dApos : 0≤(deltaA L:ℝ) := by positivity
  have enough : h≤l+g+d+2*a := by dsimp [d]; linarith
  have ratio := ThresholdCoarseDensity.small_ratio cut small
  have half := ThresholdReceiverScale.good_half t E h l d a g (by linarith) ratio th dsq low ands enough
  have size := ThresholdReceiverScale.receiver_size w l a E one wbound low ands
  exact ⟨half,size,ThresholdReceiverScale.receiver_dense t E h g w cut (by linarith)
    (by dsimp [g]; positivity) (by dsimp [w]; positivity) small th half size⟩
end ThresholdReceiverWindow
