import ThresholdHubDegrees
import ThresholdHighComponents
import ThresholdDegreeBudget
import ThresholdRegularLedger
namespace ThresholdReceiverAndBudget
open PEqualNP.CircuitLowerBounds ThresholdHubDegrees ThresholdHighComponents ThresholdSharedPartition
open ThresholdSimpleIncidence ThresholdRegularSource ThresholdOrExtraction ThresholdOrGroups
open ThresholdFanoutBudget T2SoleOrSplice T2CubeDeletion T2RegularOrDelete
theorem physical {n out : Nat} {gs : List ResidualSurplus.Raw} (hn : 2≤n)
    (M : LexMinimum n (source gs out)) (reg : Regular n gs) :
    let C := source gs out
    let L := layout n gs out M.eligible
    let h := (hubs C n).card
    let c := Nat.card (graph L).ConnectedComponent
    n+(internal L).card+h*((andIds C).length+2*n) ≤
      (missed L).card+h*(C.size+4+c) := by
  classical
  intro C L h c
  obtain ⟨two,inj,D,dm,rep,price⟩ := classified_simple hn M reg
  rw [←vertices_card] at price
  have full := M.eligible.1
  have mono := ThresholdPublicMinimum.eligible_mono M.eligible
  have partition := ThresholdGlobalGlue.count_partition C
  have bound (u : T2OrPartition.Id C) :
      (raws L u).card+((andIds C).length+2*n) ≤ C.size+4+c := by
    by_cases mem : u∈vertices L
    · let v : ThresholdGraphCounts.Vtx L := ⟨u,mem⟩
      have b := ThresholdGlobalGlue.physical_degree_budget L v mono full two inj D dm rep price
      rw [ThresholdGraphCounts.degree_eq_raw L v two inj] at b
      change (raws L u).card+2*n≤ors C.gates+4+c at b
      change (andIds C).length+ors C.gates=C.size at partition
      omega
    · have none : raws L u=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        exact fun x hx => mem (active_endpoint L x (Finset.mem_filter.mp hx).2)
      have b := ThresholdGlobalGlue.original_or_floor C mono full
      change (andIds C).length+ors C.gates=C.size at partition
      simp [none]; omega
  have sum := Finset.sum_le_sum (s:=hubs C n) (fun u _ => bound u)
  have identity : (∑ u∈hubs C n, (raws L u).card)+(missed L).card=n+(internal L).card := sum_degrees L two
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at sum
  have ledger : (∑ u∈hubs C n, (raws L u).card)+h*((andIds C).length+2*n)≤h*(C.size+4+c) := by
    simpa only [h,Nat.mul_add,Nat.cast_id] using sum
  omega

theorem count_real (t n s h e m M c a l E : ℝ)
    (one : 1≤E) (hbig : 1≤h) (sq : t^2=2*n) (exc : s≤t+E)
    (sum : n+m+h*a ≤ e+h*(s+4+c)) (raw : 2*(m+M)=h*(h-1))
    (avoid : e≤4) (low : l≤730*E) (components : c≤1+l+e) (miss : M≤180*h*E) :
    a≤930*E := by
  have hs : 0<h := by linarith
  have caps : s+4+c ≤ t+731*E+9 := by linarith
  have pays := mul_le_mul_of_nonneg_left caps hs.le
  have he := mul_le_mul_of_nonneg_right hbig (show 0≤E by linarith)
  have hc := mul_le_mul_of_nonneg_left one hs.le
  apply (mul_le_mul_iff_right₀ hs).mp
  nlinarith only [sum,raw,avoid,miss,pays,he,hc,one,hbig,sq,sq_nonneg (t-h)]
end ThresholdReceiverAndBudget
