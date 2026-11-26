import ThresholdNativeCoarse
import ThresholdReceiverWindow
import ThresholdNativeStarCap
import ThresholdThirdPower
namespace ThresholdRegularThird
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdRegularSource ThresholdSharedPartition
open ThresholdHighComponents ThresholdSecondaryReceivers T2SoleOrSplice T2RegularOrDelete T2CubeDeletion

theorem fine_scale {h t E d B l M : ℝ} (h4 : 4≤h) (t0 : 0≤t) (e1 : 1≤E)
    (th : t≤2*h) (d0 : 0≤d) (dB : d^2+5*d≤B) (Bt : B≤12*t*E)
    (lB : l*h≤20*B) (mB : M≤5*B) :
    d^2≤32*t*E ∧ l≤730*E ∧ M≤180*h*E := by
  have e0 : 0≤E := by linarith
  have te := mul_le_mul_of_nonneg_right th e0
  have he := mul_nonneg (show 0≤h by linarith) e0
  have hpos : 0<h := by linarith
  refine ⟨by nlinarith only [mul_nonneg t0 e0,d0,dB,Bt],?_,?_⟩
  · apply (mul_le_mul_iff_left₀ hpos).mp
    nlinarith only [lB,Bt,te,he]
  · nlinarith only [mB,Bt,te,he]

theorem physical_power {n out : Nat} {gs : List Raw} (hn : 5≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs) (t E : ℝ)
    (sq : t^2=2*(n:ℝ)) (cut : (2:ℝ)^200≤t)
    (exc : E=1+max 0 (((source gs out).size:ℝ)-2*n-t)) (small : E^5≤t^3)
    (rough : 32*(ThresholdHubMissing.M (layout n gs out minim.eligible):ℤ)≤
      ((hubs (source gs out) n).card:ℤ)*(hubs (source gs out) n).card)
    (cycles :
      let C := source gs out
      let L := layout n gs out minim.eligible
      let g := (good C n (high L)).card
      let w := (receivers C n (high L)).card
      0<g → w^3≤g^2 → g^4≤12*ThresholdHubMissing.M L*w^4) :
    t^3≤(2:ℝ)^65*E^5 := by
  let C := source gs out
  let L := layout n gs out minim.eligible
  let h : ℝ := (hubs C n).card
  let s : ℝ := (C.size:ℝ)-2*n
  let d := s+1-h
  let B := s^2+7*s+14-t^2
  let l : ℝ := ((hubs C n) \ high L).card
  let M : ℝ := ThresholdHubMissing.M L
  let g : ℝ := (good C n (high L)).card
  let w : ℝ := (receivers C n (high L)).card
  have tt : 0≤t := by linarith
  have e1 : 1≤E := by rw [exc]; linarith [le_max_left 0 ((C.size:ℝ)-2*n-t)]
  have se : s≤t+E := by dsimp [s]; rw [exc]; linarith [le_max_right 0 ((C.size:ℝ)-2*n-t)]
  obtain ⟨_,d0,dB,th,_,bt,h4⟩ := ThresholdNativeCoarse.parameters hn minim reg t E sq cut exc small
  change 4≤h at h4
  have hReal : (4:ℝ)≤((hubs C n).card:ℝ) := h4
  have hZ : 4≤((hubs C n).card:ℤ) := by exact_mod_cast hReal
  obtain ⟨li,mi,_⟩ := ThresholdHubFine.regular_fine hn minim reg
    (ThresholdNativeStarSaving.regular_star_cap (by omega) minim reg) hZ rough
  have eqB : ((ThresholdHubFine.budget n C.size:ℤ):ℝ)=B := by
    dsimp [ThresholdHubFine.budget,ThresholdHubDeficits.surplus,B,s]
    push_cast
    rw [sq]
  have lR : l*h≤20*B := by rw [←eqB]; dsimp only [l,h]; exact_mod_cast li
  have mR : M≤5*B := by rw [←eqB]; dsimp only [M]; exact_mod_cast mi
  have ⟨dscale,lscale,mscale⟩ := fine_scale h4 tt e1 th d0 dB bt lR mR
  obtain ⟨hg,wr,den⟩ := ThresholdReceiverWindow.window hn minim reg t E cut e1 small sq se th
    (by linarith : 1≤h) dscale lscale mscale
  change h≤2*g at hg
  change w^3≤g^2 at den
  have gpos : 0<g := by linarith
  have cp : g^4≤12*M*w^4 := by
    dsimp only [g] at gpos
    dsimp only [g,w] at den
    dsimp only [g,M,w]
    exact_mod_cast cycles (by exact_mod_cast gpos) (by exact_mod_cast den)
  have mpos : 0≤M := by dsimp [M]; positivity
  exact ThresholdThirdPower.ledger_power t h E M w g (24*M) tt (by linarith) (by linarith)
    mpos (by dsimp [w]; positivity) (by positivity) th hg mscale wr le_rfl (by linarith)
end ThresholdRegularThird
