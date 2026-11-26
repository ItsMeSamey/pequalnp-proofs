import ThresholdHubDegrees
namespace ThresholdHubDeficits
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrExtraction ThresholdRegularSource
open ThresholdSimpleIncidence ThresholdSharedPartition ThresholdSharedFlow ThresholdFlowPairs
open ThresholdHubDegrees ThresholdFlowSum T2OrPartition
open scoped BigOperators
variable {C : Circuit} {n : Nat} (L : Layout C n)
def surplus (n g : Nat) : ℤ := (g:ℤ)-2*(n:ℤ)
noncomputable def D (u : Id C) : ℤ :=
  surplus n C.size + 3 - ((before L u).card:ℤ) - ((raws L u).card:ℤ)

theorem direct_arithmetic {n s h d miss m P b Ksum : ℤ}
    (h0 : 0≤h) (d0 : 0≤d) (fund : d+h≤s+1)
    (zero : miss≤4) (parts : n=miss+m+b)
    (edge : b≤3*h+P+h*d) (ledger : Ksum=h*(s+3)-P-(n-miss+m)) :
    Ksum≤s^2+7*s+14-2*n := by
  have hf := mul_le_mul_of_nonneg_left (show d≤s+1-h by omega) h0
  have gap := mul_nonneg (show 0≤s+1-h by omega) (show 0≤s+6-h by omega)
  nlinarith only [parts,edge,ledger,zero,hf,gap]

theorem deficit_sum (two : ∀ x,(endpoints L x).card=2)
    (avoid : (missed L).card≤4)
    (leaf : ∀ u∈hubs C n, (singleAt L u).card≤1+max (fan L u) (leak L u))
    (fund : deltaO L+deltaA L+(hubs C n).card+2*n≤C.size+1) :
    ∑ u∈hubs C n,D L u ≤ (surplus n C.size)^2+7*(surplus n C.size)+14-2*(n:ℤ) := by
  classical
  let H := hubs C n
  let s := surplus n C.size
  let b := ∑ u∈H,(singleAt L u).card
  let p := (hotPairs L).card
  let e := (missed L).card
  let m := (internal L).card
  let d := deltaO L+deltaA L
  have part : n=e+m+b := partition L
  have orig := boundary L leaf
  have finance : d+H.card+2*n≤C.size+1 := fund
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
  have hand : (∑ u∈H,(raws L u).card)+e=n+m := sum_degrees L two
  have predecessors : (∑ u∈H,(before L u).card)=p := sum_before L
  have hand' : (∑ u∈H,((raws L u).card:ℤ))+(e:ℤ)=(n:ℤ)+(m:ℤ) := by exact_mod_cast hand
  have pred' : (∑ u∈H,((before L u).card:ℤ))=(p:ℤ) := by exact_mod_cast predecessors
  have ledger : (∑ u∈H,D L u)=(H.card:ℤ)*(s+3)-(p:ℤ)-((n:ℤ)-(e:ℤ)+(m:ℤ)) := by
    simp only [D,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,pred']
    dsimp only [s]
    omega
  apply direct_arithmetic (h := (H.card:ℤ)) (d := (d:ℤ)) (miss := (e:ℤ)) (m := (m:ℤ))
    (P := (p:ℤ)) (b := (b:ℤ)) (by positivity) (by positivity) _ _ _ _ ledger
  · change (d:ℤ)+(H.card:ℤ)≤(C.size:ℤ)-2*(n:ℤ)+1; omega
  · exact_mod_cast avoid
  · exact_mod_cast part
  · exact_mod_cast priv

open T2CubeDeletion T2SoleOrSplice T2RegularOrDelete
theorem regular_deficit_budget {n out : Nat} {gs : List Raw} (hn : 5≤n)
    (M : LexMinimum n (source gs out)) (reg : Regular n gs) :
    let C := source gs out
    let L := layout n gs out M.eligible
    (∀ u∈hubs C n,0≤D L u) ∧
    ∑ u∈hubs C n,D L u≤(surplus n C.size)^2+7*(surplus n C.size)+14-2*(n:ℤ) := by
  intro C L
  have simple := classified_simple (by omega : 2≤n) M reg
  have structure' := ThresholdSharpEndpoint.structure_of_star ThresholdStarBypass.regular_star_boundary n hn gs out M reg
  have fund : deltaO L+deltaA L+(hubs C n).card+2*n≤C.size+1 := by
    simpa only [deltaO,deltaA,fan_readers,ThresholdSharedFunding.extrasOr,
      ThresholdSharedFunding.extrasAnd,ThresholdSharedFunding.fan] using ThresholdSharedFunding.funding M reg
  refine ⟨?_,deficit_sum L simple.1 structure'.missed_bound structure'.leaf_bound fund⟩
  intro u hu
  have cap := physical_degree_cap L u hu simple.1 simple.2.1 structure'.no_shared_raw (structure'.leaf_bound u hu) fund
  unfold D surplus
  omega
#print axioms direct_arithmetic
#print axioms regular_deficit_budget
end ThresholdHubDeficits
