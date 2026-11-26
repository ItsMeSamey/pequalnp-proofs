import ThresholdNativeSelectedMoments
import ThresholdUniformMiddle
import ThresholdSharpGraphAssembly
namespace ThresholdPhysicalMiddlePacking
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2RegularOrDelete T2CubeDeletion
open T2OrPartition ThresholdOrExtraction ThresholdRegularSource ThresholdSharedPartition ThresholdHighComponents
open ThresholdEffectiveColumns ThresholdSecondaryReceivers ThresholdPurityPins ThresholdFanoutBudget
open ThresholdFlowSum ThresholdNativeColumnCharge ThresholdNativeRowSelection ThresholdUniformMiddle
variable {n out : Nat} {gs : List Raw} (minim : LexMinimum n (source gs out)) (reg : Regular n gs)
local notation "Cir" => source gs out
local notation "Lay" => layout n gs out minim.eligible
local notation "HH" => high Lay
local notation "Hubs" => hubs Cir n
local notation "kk" => ((ThresholdHubFine.budget n (Circuit.size Cir):ℤ):ℝ)/2
local notation "hh" => (Finset.card Hubs:ℝ)
local notation "lowN" => Finset.card (Hubs \ HH)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 900000 in
include reg in
theorem packing (hn : 5≤n) (t E P X u : ℝ) (p : 1048576≤P) (big : P^100≤X) (tol : 1≤P*u)
    (hp : 0<hh) (ep : 0<E) (lo : X^10≤2*hh) (hi : hh≤2*X^10)
    (elo : X^6≤65536*E) (ord : (1-u)*t≤hh)
    (mCap : (ThresholdHubMissing.M Lay:ℝ)≤P^2*X^16)
    (lowCap : (lowN:ℝ)≤P^2*X^6) (andCap : ((andIds Cir).length:ℝ)≤P^2*X^6)
    (vCap : ((receivers Cir n HH).card:ℝ)≤P^2*X^6)
    (impCap : ((impure Lay HH).card:ℝ)≤8*P^2*X^6) (deltaCap : (deltaO Lay:ℝ)≤4*P*X^8)
    (budget : kk≤(1+3*(u/10))*hh*E) :
    Nonempty (ThresholdSharpGlobalLower.RelativeLedger (n:ℝ) t E u) := by
  classical
  let H := HH
  let h := (Hubs).card
  let low := lowN
  let T := trimCost Lay
  let holes := (inner Lay H).card
  let V := (receivers Cir n H).card
  have pp : 1≤P := by linarith
  have xp : P≤X := (show P≤P^100 by simpa using pow_le_pow_right₀ pp (by decide : 1≤100)).trans big
  have xx : 1≤X := pp.trans xp
  have x0 : 0≤X := by linarith
  have scale : 100*P≤X^2 := by nlinarith only [xp,mul_nonneg (show 0≤X-100 by linarith only [xp,p]) x0]
  have subH : H⊆Hubs := Finset.filter_subset _ _
  have highCap := Finset.card_le_card subH
  have ret : retained Lay⊆H := by
    intro r hr
    exact (Finset.mem_filter.mp (good_pure Lay (Finset.mem_sdiff.mp hr).1).1).1
  have tr : T≤2*ThresholdHubMissing.M Lay+h+2*h*low := by
    have rh := Finset.card_le_card (ret.trans subH)
    have mul := Nat.mul_le_mul_right low (Nat.mul_le_mul_left 2 highCap)
    change 2*ThresholdHubMissing.M Lay+(retained Lay).card+2*H.card*low≤_
    change (retained Lay).card≤h at rh
    change 2*H.card*low≤2*h*low at mul
    omega
  have part : H.card+low=h := by
    have eq := Finset.card_sdiff_add_card_eq_card subH
    change low+H.card=h at eq
    omega
  obtain ⟨mu,room,space,subcost⟩ := nat_room (by linarith : 100≤P) xx scale lo hi lowCap part mCap tr
  obtain ⟨R,rr,j,A,D,row,choose,credit,adj,nc,nf,wed⟩ := selected_moments hn minim reg room space
  let w := (R.biUnion (effective Lay minim)).card
  let g := R.card
  let F := holes+2*H.card*low
  have gh : g≤h := Finset.card_le_card (rr.trans (ret.trans subH))
  have width : w≤V := by
    have sub : R.biUnion (effective Lay minim) ⊆ (receivers Cir n H).image (column Lay minim) := by
      intro v hv
      obtain ⟨r,hr,ev⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ev
      exact Finset.mem_image.mpr ⟨s,Finset.mem_biUnion.mpr ⟨r,(good_pure Lay (Finset.mem_sdiff.mp (rr hr)).1).1,hs⟩,rfl⟩
    exact (Finset.card_le_card sub).trans Finset.card_image_le
  have hw : (w:ℝ)≤P^2*X^6 := (by exact_mod_cast width : (w:ℝ)≤(V:ℝ)).trans vCap
  have simple := ThresholdSimpleIncidence.classified_simple (by omega : 2≤n) minim reg
  have st := ThresholdSharpEndpoint.structure_of_star ThresholdStarBypass.regular_star_boundary n hn gs out minim reg
  have q := card_unspent Lay simple.1 simple.2.1 st.no_shared_raw
  have hole : holes≤ThresholdHubMissing.M Lay := by
    have count : holes≤(unspent Lay).card := Finset.card_le_card (Finset.filter_subset _ _)
    rw [q] at count
    exact count.trans (Nat.sub_le _ _)
  have coarse : (F:ℝ)≤6*P^2*X^16 := by
    have hc : (H.card:ℝ)≤2*X^10 := (by exact_mod_cast highCap : (H.card:ℝ)≤(h:ℝ)).trans hi
    have pay := mul_le_mul hc lowCap (show 0≤(low:ℝ) by positivity) (show 0≤2*X^10 by positivity)
    have z : (holes:ℝ)≤P^2*X^16 := (by exact_mod_cast hole : (holes:ℝ)≤(ThresholdHubMissing.M Lay:ℝ)).trans mCap
    change (low:ℝ)≤_ at lowCap
    change (H.card:ℝ)*(low:ℝ)≤_ at pay
    dsimp only [F]; push_cast
    nlinarith only [z,pay,show 0≤P^2*X^16 by positivity]
  obtain ⟨z,yx,_⟩ := scales (by linarith : 100≤P) xx scale
  have ch := ThresholdSharpArithmetic.twice_choose_two j
  have chR : 2*((j.choose 2:Nat):ℝ)=(j:ℝ)*(j-1:ℝ) := by exact_mod_cast ch
  have jcap := private_count z mCap (by
    rw [←chR]; exact_mod_cast Nat.mul_le_mul_left 2 choose)
  change H.card≤g+(impure Lay H).card+deltaO Lay+3*(andIds Cir).length+4*j+T.sqrt+2*V at row
  have gr : (h:ℝ)≤g+low+(impure Lay H).card+deltaO Lay+3*(andIds Cir).length+4*j+T.sqrt+2*V := by
    exact_mod_cast (show h≤g+low+(impure Lay H).card+deltaO Lay+3*(andIds Cir).length+4*j+T.sqrt+2*V by omega)
  have ghR : (g:ℝ)≤(h:ℝ) := by exact_mod_cast gh
  have rows := row_error (by linarith : 100≤P) z yx ghR gr lowCap impCap deltaCap andCap jcap mu vCap
  rw [abs_of_nonneg (sub_nonneg.mpr ghR)] at rows
  have col : ((h:ℝ)-(low:ℝ)-4*(T.sqrt:ℝ))*(w:ℝ)+(holes:ℝ)≤kk := by
    change 2*(((h-(low+4*T.sqrt):Nat):ℤ)*(w:ℤ)+(holes:ℤ))≤_ at credit
    have pos : low+4*T.sqrt≤h := subcost
    have natEq : h-(low+4*T.sqrt)+(low+4*T.sqrt)=h := Nat.sub_add_cancel pos
    have eqR : ((h-(low+4*T.sqrt):Nat):ℝ)+(low+4*(T.sqrt:ℝ))=h := by exact_mod_cast natEq
    have cv : 2*(((h-(low+4*T.sqrt):Nat):ℝ)*(w:ℝ)+(holes:ℝ))≤((ThresholdHubFine.budget n (Cir).size:ℤ):ℝ) := by exact_mod_cast credit
    rw [show (h:ℝ)-low-4*(T.sqrt:ℝ)=((h-(low+4*T.sqrt):Nat):ℝ) by linarith only [eqR]]
    linarith
  have u0 : 0≤u := by by_contra! neg; linarith only [tol,mul_neg_of_pos_of_neg (show 0<P by linarith only [p]) neg]
  have pu : 1≤u*P := by rw [mul_comm]; exact tol
  have p4 : P^4≤X := (pow_le_pow_right₀ pp (by decide : 4≤100)).trans big
  have p2 : P^2≤X := (pow_le_pow_right₀ pp (by decide : 2≤100)).trans big
  have giant : 4000000≤X := by nlinarith only [p,p2,sq_nonneg (P-3)]
  have powCap := mul_le_mul p4 giant (by norm_num : (0:ℝ)≤4000000) x0
  have px : 4000000*P^3≤u*X^2 := by
    have p3 := mul_le_mul_of_nonneg_right pu (show 0≤4000000*P^3 by positivity)
    have cost := mul_le_mul_of_nonneg_left powCap u0
    nlinarith only [p3,cost]
  have bigCost := mul_le_mul_of_nonneg_right px (show 0≤X^14 by positivity)
  have he := mul_le_mul lo elo (show 0≤X^6 by positivity) (show 0≤2*(h:ℝ) by positivity)
  have reserve := mul_le_mul_of_nonneg_left he u0
  have d0 : (low:ℝ)+4*(T.sqrt:ℝ)≤13*P*X^8 := by linarith only [lowCap,yx,mu]
  have loss := mul_le_mul d0 hw (show 0≤(w:ℝ) by positivity) (show 0≤13*P*X^8 by positivity)
  have refund : ((low:ℝ)+4*(T.sqrt:ℝ))*w≤(u/2)*h*E := by
    nlinarith only [loss,bigCost,reserve,show 0≤P^3*X^14 by positivity]
  have cols : (w:ℝ)≤(1-(holes:ℝ)/((h:ℝ)*E)+u)*E := by
    have divEq := div_mul_cancel₀ (holes:ℝ) (mul_pos hp ep).ne'
    have pay := mul_nonneg u0 (mul_nonneg hp.le ep.le)
    apply (le_of_mul_le_mul_left ?_ hp)
    nlinarith only [col,budget,refund,divEq,pay]
  apply ThresholdSharpGlobalLower.graph_ledger (P:=P) (X:=X) (h:=(h:ℝ)) (w:=(w:ℝ)) (g:=(g:ℝ))
    (A:=(A:ℝ)) (D:=(D:ℝ)) (coarse:=(F:ℝ)) (holes:=(holes:ℝ)) p big tol lo hi elo hp ep
    (Nat.cast_nonneg w) (Nat.cast_nonneg g) (Nat.cast_nonneg A) (Nat.cast_nonneg D) (Nat.cast_nonneg F) (Nat.cast_nonneg holes)
    ghR rows hw coarse _ _ _ _ cols ord
  · exact_mod_cast adj
  · exact_mod_cast nc
  · exact_mod_cast nf
  · have cast : (2*(g:ℝ))^2≤(w:ℝ)*(2*((A:ℝ)+(D:ℝ))+2*g) := by exact_mod_cast wed
    nlinarith only [cast]
#print axioms packing
end ThresholdPhysicalMiddlePacking
