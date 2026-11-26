import ThresholdSharpNativeWindow
import ThresholdSharpScaleRatio
import ThresholdUniformMiddle
import ThresholdPurityPins
import ThresholdRegularThirdCore
namespace ThresholdSharpNativeWindow
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdRegularSource ThresholdSharedPartition
open ThresholdHighComponents ThresholdSecondaryReceivers ThresholdPurityPins ThresholdFlowSum ThresholdSharedFlow ThresholdFanoutBudget
open T2SoleOrSplice T2RegularOrDelete T2CubeDeletion
theorem bands {n out : ℕ} {gs : List Raw} (hn : 5≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs) (P X t E u : ℝ)
    (root : t=Real.sqrt (2*(n:ℝ))) (sur : E=((source gs out).size:ℝ)-2*n-t)
    (pp : (2:ℝ)^80≤P) (big : P^100≤X) (time : X^10=t)
    (elo : X^6≤(2:ℝ)^16*E) (ehi : E≤P*X^6)
    (tol : (2:ℝ)^20≤(u/10)*P) (up : 0<u) (us : u≤1/1000) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    let h : ℝ := (hubs C n).card
    let K := (ThresholdHubFine.budget n C.size:ℝ)/2
    let H := high L
    0<E ∧ 0<h ∧ (1-u)*t≤h ∧ t≤2*h ∧ h≤2*t ∧ K≤(1+3*(u/10))*h*E ∧
      (((hubs C n) \ H).card:ℝ)≤P^2*X^6 ∧ ((andIds C).length:ℝ)≤P^2*X^6 ∧
      ((receivers C n H).card:ℝ)≤P^2*X^6 ∧ (ThresholdHubMissing.M L:ℝ)≤P^2*X^16 ∧
      (deltaO L:ℝ)≤4*P*X^8 ∧ ((impure L H).card:ℝ)≤8*P^2*X^6 := by
  intro C L h K H
  let s := (C.size:ℝ)-2*(n:ℝ)
  let d := s+1-h
  let E₀ := 1+max 0 E
  let low : ℝ := ((hubs C n) \ H).card
  let a : ℝ := (andIds C).length
  have p : 10000≤P := by norm_num at pp; linarith
  have p1 : 1≤P := by linarith
  have px : P≤X := (show P≤P^100 by simpa using (pow_le_pow_right₀ p1 (by decide : 1≤100))).trans big
  have x1 : 1≤X := p1.trans px
  have xn := (by linarith : 0≤X)
  have x6 : X≤X^6 := by simpa using (pow_le_pow_right₀ x1 (by decide : 1≤6))
  have e14 : 14≤E := by norm_num at pp elo; linarith
  have ep : 0<E := by linarith
  have e0 : E₀=1+E := by simp [E₀,max_eq_right ep.le]
  have sq : t^2=2*(n:ℝ) := by rw [root]; exact Real.sq_sqrt (by positivity)
  have ex : E₀=1+max 0 (((source gs out).size:ℝ)-2*(n:ℝ)-t) := by rw [←sur]
  have st : s=t+E := by dsimp [s,C]; linarith
  obtain ⟨ratio,cut⟩ := ThresholdSharpScaleBand.coarse_ratio P X t E pp px time (by linarith) ehi
  obtain ⟨_,d0,charge,th,ht,cap,h4⟩ := ThresholdNativeRatio.parameters hn minim reg t E₀ sq cut ex ratio
  change 4≤h at h4
  have eqK : 2*K=s^2+7*s+14-t^2 := by
    dsimp [K,ThresholdHubFine.budget,ThresholdHubDeficits.surplus,s]
    push_cast
    rw [sq]
    <;> ring
  have dcharge : d^2+5*d≤2*K := by rw [eqK]; exact charge
  have dn : 0≤d := d0
  have disc : 2*K=2*t*E+E^2+7*t+7*E+14 := by rw [eqK,st]; ring
  have p20 : (2:ℝ)^20≤P := by norm_num at pp ⊢; linarith
  have budget := ThresholdSharpScaleBand.budget_from_scale t E K P X px p20 time.symm elo ehi disc
  have ⟨lh,hh⟩ := ThresholdSharpScaleBand.hub_band h t E d K P X x1 p1 ep.le
    (by dsimp [d]; rw [st]) dn (by linarith) budget time.symm ehi
  obtain ⟨ord,half,twice,rel⟩ := ThresholdSharpScaleBand.relative t E h K P X (u/10) (by linarith)
    px (by positivity) (by linarith) tol time.symm elo ehi lh hh disc
  have hReal : (4:ℝ)≤((hubs C n).card:ℝ) := h4
  have hz : (4:ℤ)≤((hubs C n).card:ℤ) := by exact_mod_cast hReal
  obtain ⟨li,mi,_⟩ := ThresholdHubFine.regular_fine hn minim reg
    (ThresholdNativeStarSaving.regular_star_cap (by omega) minim reg) hz
    (ThresholdNativeRatio.rough hn minim reg t E₀ sq cut ex ratio)
  have k2 : 2*K=(ThresholdHubFine.budget n C.size:ℝ) := by dsimp [K]; ring
  have lR : low*h≤20*(2*K) := by rw [k2]; dsimp only [low,h,H]; exact_mod_cast li
  have mR : (ThresholdHubMissing.M L:ℝ)≤5*(2*K) := by rw [k2]; exact_mod_cast mi
  have tp : 0≤t := by rw [←time]; positivity
  obtain ⟨dBound,lBound,mBound⟩ := ThresholdRegularThird.fine_scale h4 tp (by rw [e0]; linarith : 1≤E₀)
    half dn dcharge (by rw [eqK]; exact cap) lR mR
  obtain ⟨aa,vv,dd⟩ := counts hn minim reg t E₀ (by rw [e0]; linarith) sq
    (show s≤t+E₀ by rw [st,e0]; linarith) half (by linarith) dBound lBound mBound
  have e2 : E₀≤2*(P*X^6) := by rw [e0]; linarith
  have widths (q : ℝ) (b : q≤3000*E₀) : q≤P^2*X^6 := by
    have mul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show 6000≤P by linarith) (by linarith : 0≤P)) (pow_nonneg xn 6)
    nlinarith only [mul,b,e2]
  have a0 : a≤3000*E₀ := by change a≤930*E₀ at aa; linarith [show 0≤E₀ by rw [e0]; linarith]
  have lo : low≤3000*E₀ := by linarith [show 0≤E₀ by rw [e0]; linarith]
  have mq : (ThresholdHubMissing.M L:ℝ)≤P^2*X^16 := by
    have ae := mul_le_mul_of_nonneg_left ehi tp
    have pp' := mul_le_mul_of_nonneg_right (show 20≤P by linarith) (by linarith : 0≤P)
    have factor := mul_le_mul_of_nonneg_right pp' (pow_nonneg xn 16)
    rw [←time] at ae budget
    nlinarith only [mR,budget,ae,factor]
  have dq : d≤4*P*X^8 := by
    have ae := mul_le_mul_of_nonneg_left ehi tp
    have sf := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right p1 (by linarith : 0≤P)) (pow_nonneg xn 16)
    rw [←time] at ae budget
    by_contra! bad
    have b := pow_lt_pow_left₀ bad (by positivity : 0≤4*P*X^8) (by decide : (2:ℕ)≠0)
    nlinarith only [dcharge,dn,budget,ae,sf,b]
  have purity := ThresholdPurityPins.regular_purity_product hn minim reg
  have pr : h*((impure L H).card:ℝ)≤2*K+h*(5*a+2*low-2) := by
    rw [k2]; dsimp only [h,H,a,low,ThresholdHubFine.budget]
    exact_mod_cast purity
  have imp := ThresholdUniformMiddle.impurity (by linarith : 8≤P) xn (by linarith : 0<h)
    (by rw [time]; exact budget) (by rw [time]; exact half) ep.le ehi (widths _ a0) (widths _ lo) pr
  exact ⟨ep,by linarith,by nlinarith only [ord,mul_nonneg up.le tp],half,twice,rel,widths _ lo,
    widths _ a0,widths _ vv,mq,le_trans dd dq,imp⟩
end ThresholdSharpNativeWindow
