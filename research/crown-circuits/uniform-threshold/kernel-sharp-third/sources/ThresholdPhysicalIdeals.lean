import ThresholdHubDeficits
import ThresholdAlreadyHot
import ThresholdProbeOrder
import ThresholdPrefixDensity
namespace ThresholdPhysicalIdeals
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2RegularOrDelete T2CubeDeletion
open ThresholdSharedPartition ThresholdFlowPairs ThresholdSharedFlow ThresholdRegularSource
open ThresholdSimpleIncidence ThresholdHubDegrees ThresholdHubDeficits ThresholdProbeIdeals
open ThresholdOrExtraction T2OrPartition
variable {C : Circuit} {n : Nat} (L : Layout C n)
theorem mem_pair (a b : Id C) : (a,b)∈hotPairs L ↔
    (a∈hubs C n ∧ b∈hubs C n) ∧ a≠b ∧ active L a b=true := by simp [hotPairs]

theorem trans : Trans (hotPairs L) := by
  intro a b c ab bc
  obtain ⟨⟨ha,_⟩,ne,first⟩ := (mem_pair L a b).mp ab
  obtain ⟨⟨_,hc⟩,ne',second⟩ := (mem_pair L b c).mp bc
  exact (mem_pair L a c).mpr ⟨⟨ha,hc⟩,ne_of_lt (lt_trans (oriented L ne first) (oriented L ne' second)),
    ThresholdSharedFlow.active_trans L first second⟩

theorem succ_eq (u : Id C) (hu : u∈hubs C n) :
    succCount (hotPairs L) u=(after L u).card := by
  classical
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    obtain ⟨inQ,e⟩ := Finset.mem_filter.mp hp
    obtain ⟨⟨_,hv⟩,ne,on⟩ := (mem_pair L p.1 p.2).mp inQ
    exact Finset.mem_filter.mpr ⟨hv,e ▸ ne,e ▸ on⟩
  · intro p hp q hq eq
    exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) eq
  · intro b hb
    obtain ⟨hb,ne,on⟩ := Finset.mem_filter.mp hb
    exact ⟨(u,b),Finset.mem_filter.mpr ⟨(mem_pair L u b).mpr ⟨⟨hu,hb⟩,ne,on⟩,rfl⟩,rfl⟩

theorem pred_eq (u : Id C) (hu : u∈hubs C n) :
    predCount (hotPairs L) u=(before L u).card := by
  classical
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    obtain ⟨inQ,e⟩ := Finset.mem_filter.mp hp
    obtain ⟨⟨hv,_⟩,ne,on⟩ := (mem_pair L p.1 p.2).mp inQ
    exact Finset.mem_filter.mpr ⟨hv,e ▸ ne,e ▸ on⟩
  · intro p hp q hq eq
    exact Prod.ext eq ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
  · intro b hb
    obtain ⟨hb,ne,on⟩ := Finset.mem_filter.mp hb
    exact ⟨(b,u),Finset.mem_filter.mpr ⟨(mem_pair L b u).mpr ⟨⟨hb,hu⟩,ne,on⟩,rfl⟩,rfl⟩

theorem high_antichain {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) :
    let C := source gs out
    let L := layout n gs out M.eligible
    Anti (hotPairs L) ((hubs C n).filter (fun i => (hubs C n).card<2*(neighbors L i).card)) := by
  intro C L
  apply high_anti _ _ (neighbors L) (fun _ => Finset.filter_subset _ _)
  intro a b pair
  obtain ⟨_,ab,hot⟩ := (mem_pair L a b).mp pair
  apply Finset.disjoint_left.mpr
  intro v va vb
  obtain ⟨_,va',x,ux⟩ := Finset.mem_filter.mp va
  obtain ⟨_,vb',y,vy⟩ := Finset.mem_filter.mp vb
  have xy : x≠y := by
    intro same; subst y
    have eq := ux.symm.trans vy
    have m : a∈({b,v} : Finset (Id C)) := eq ▸ (by simp : a∈({a,v} : Finset (Id C)))
    simp [ab,Ne.symm va'] at m
  exact ThresholdAlreadyHot.no_common_raw M reg x y xy a b v (by change a∈endpoints L x; rw [ux]; simp) (by change v∈endpoints L x; rw [ux]; simp) (by change endpoints L y⊆{b,v}; rw [vy]) hot

theorem regular_ideal_cut {n out : Nat} {gs : List Raw} (hn : 5≤n)
    (M : LexMinimum n (source gs out)) (reg : Regular n gs) :
    let C := source gs out
    let L := layout n gs out M.eligible
    (∀ u∈hubs C n,(raws L u).card+(after L u).card+2*n≤C.size+3) →
    ∀ I,Ideal (hotPairs L) I → ((Cut (hotPairs L) I).card:ℤ)≤
      (surplus n C.size)^2+7*(surplus n C.size)+14-2*(n:ℤ) := by
  classical
  intro C L star I ideal
  let H := hubs C n
  let J := I∩H
  have sub : J⊆H := Finset.inter_subset_right
  have jj : Ideal (hotPairs L) J := by
    intro a b ab bj
    have h := (mem_pair L a b).mp ab
    exact Finset.mem_inter.mpr ⟨ideal a b ab (Finset.mem_of_mem_inter_left bj),h.1.1⟩
  have eq : Cut (hotPairs L) J=Cut (hotPairs L) I := by
    ext p
    by_cases z : p∈hotPairs L
    · have h := (mem_pair L p.1 p.2).mp z
      have left : p.1∈H := h.1.1
      have right : p.2∈H := h.1.2
      simp [Cut,J,z,left,right]
    · simp [Cut,z]
  have regD := regular_deficit_budget hn M reg
  have cap (u) (hu : u∈J) : (succCount (hotPairs L) u:ℤ) ≤ (predCount (hotPairs L) u:ℤ)+D L u := by
    have uh := sub hu
    have f := star u uh
    change (raws L u).card+(after L u).card+2*n≤(source gs out).size+3 at f
    rw [succ_eq L u uh,pred_eq L u uh]
    unfold D surplus
    omega
  have bal := cut_balance (hotPairs L) J jj
  have bal' : ((Cut (hotPairs L) J).card:ℤ)+∑ a∈J,(predCount (hotPairs L) a:ℤ)=∑ a∈J,(succCount (hotPairs L) a:ℤ) := by exact_mod_cast bal
  have sum := Finset.sum_le_sum cap
  rw [Finset.sum_add_distrib] at sum
  have larger := Finset.sum_le_sum_of_subset_of_nonneg sub (fun a ha _ => regD.1 a ha)
  rw [←eq]
  linarith [regD.2]
#print axioms regular_ideal_cut
#print axioms high_antichain
end ThresholdPhysicalIdeals
