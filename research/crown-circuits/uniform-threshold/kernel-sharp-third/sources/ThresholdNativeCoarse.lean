import ThresholdCoarseDensity
import ThresholdPublicSharp
namespace ThresholdNativeCoarse
open PEqualNP.CircuitLowerBounds ResidualSurplus T2CubeDeletion T2SoleOrSplice
open T2RegularOrDelete ThresholdSharedPartition ThresholdSharedOrBudget

theorem parameters {n out : Nat} {gs : List Raw} (hn : 5≤n)
    (M : LexMinimum n (source gs out)) (reg : Regular n gs) (t E : ℝ)
    (sq : t^2=2*(n:ℝ)) (cut : (2:ℝ)^200≤t)
    (ex : E=1+max 0 (((source gs out).size:ℝ)-2*(n:ℝ)-t))
    (small : E^5≤t^3) :
    let C := source gs out
    let h : ℝ := (hubs C n).card
    let s : ℝ := (C.size:ℝ)-2*(n:ℝ)
    let d := s+1-h
    let B := s^2+7*s+14-t^2
    0≤s ∧ 0≤d ∧ d^2+5*d≤B ∧ t≤2*h ∧ h≤2*t ∧ B≤12*t*E ∧ 4≤h := by
  intro C h s d B
  let H := (hubs C n).card
  have nd : (sharedOrs C n).Nodup :=
    ((List.nodup_finRange C.gates.length).filter _).filter _
  have number : H=(sharedOrs C n).length := List.toFinset_card_of_nodup nd
  have tally := ThresholdSharedStructural.structure_tally
    (ThresholdSharpEndpoint.structure_of_star ThresholdStarBypass.regular_star_boundary) n hn gs out M reg
  change ThresholdSharpArithmetic.Tally (n:ℤ) ((C.size:ℤ)-2*(n:ℤ)) ((sharedOrs C n).length:ℤ) at tally
  rw [←number] at tally
  unfold ThresholdSharpArithmetic.Tally at tally
  have fund := ThresholdSharedFunding.funding M reg
  have hf : H+2*n≤C.size+1 := by
    change ThresholdSharedFunding.extrasOr C n + _ + H + 2*n≤C.size+1 at fund
    omega
  have si : 0≤(C.size:ℤ)-2*(n:ℤ) := by
    by_contra! neg
    have e : H=0 := by omega
    rw [e] at tally
    simp at tally
    omega
  have s0 : 0≤s := by
    change 0≤(C.size:ℝ)-2*(n:ℝ)
    exact_mod_cast si
  have hr : (H:ℝ)+2*(n:ℝ)≤(C.size:ℝ)+1 := by exact_mod_cast hf
  have tallyR : 2*(n:ℝ)≤8+6*(H:ℝ)+H*(H-1:ℝ)+2*(H:ℝ)*((C.size:ℝ)-2*(n:ℝ)+1-H) := by
    exact_mod_cast tally
  have dd : 0≤d := by dsimp [d,s,h,H] at *; linarith only [hr]
  have gap : d^2+5*d≤B := by
    change (((C.size:ℝ)-2*(n:ℝ))+1-(H:ℝ))^2+5*(((C.size:ℝ)-2*(n:ℝ))+1-H)≤
      ((C.size:ℝ)-2*(n:ℝ))^2+7*((C.size:ℝ)-2*(n:ℝ))+14-t^2
    nlinarith only [tallyR,sq]
  have e1 : 1≤E := by rw [ex]; linarith [le_max_left 0 ((C.size:ℝ)-2*(n:ℝ)-t)]
  have se : s≤t+E := by
    change (C.size:ℝ)-2*(n:ℝ)≤t+E
    rw [ex]
    linarith [le_max_right 0 ((C.size:ℝ)-2*(n:ℝ)-t)]
  exact ⟨s0,dd,gap,ThresholdCoarseDensity.parameters cut e1
    (ThresholdCoarseDensity.small_ratio cut small) s0 se rfl (by linarith : d^2≤B) dd (by dsimp [d]; ring)⟩
end ThresholdNativeCoarse
