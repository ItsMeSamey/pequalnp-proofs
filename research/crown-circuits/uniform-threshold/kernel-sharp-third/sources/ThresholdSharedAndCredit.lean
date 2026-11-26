import ThresholdHubFine
namespace ThresholdSharedAndCredit
open PEqualNP.CircuitLowerBounds ThresholdSimpleIncidence ThresholdOrExtraction T2OrPartition
open ThresholdSharedPartition ThresholdSharedFlow ThresholdFlowPairs ResidualSurplus ThresholdFlowSum
open ThresholdHubFine ThresholdHubMissing ThresholdRegularSource T2CubeDeletion T2SoleOrSplice T2RegularOrDelete
variable {C : Circuit} {n : Nat} (L : Layout C n)
def usable := ∑ i : Id C, if L.op i=.and then fan L i-2 else 0
def sharedAnd := (Finset.univ.filter (fun i : Id C => L.op i=.and ∧ 2≤fan L i)).card

theorem decompose : usable L+sharedAnd L=deltaA L := by
  classical
  unfold usable sharedAnd deltaA
  rw [Finset.card_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases a : L.op i=.and <;> by_cases f : 2≤fan L i <;> simp [a,f] <;> omega

private theorem hub_iff (i : Id C) :
    i∈hubs C n ↔ 2≤fan L i ∧ L.op i=.or := by
  simp [hubs,ThresholdSharedOrBudget.sharedOrs,ThresholdSharedOrBudget.sharedGates,
    fan_readers,ThresholdOrExtraction.physical_op L,and_comm]

theorem row_tight (U : Id C) (member : U∈hubs C n) :
    (∑ i : Id C, ThresholdSharedFlow.budget L U i) ≤ fan L U +
    (∑ i∈hubs C n, if U≠i ∧ active L U i=true then 1 else 0) +
    (∑ i∈(hubs C n).erase U, (fan L i-2)) + usable L := by
  let H := hubs C n
  let hot := fun i : Id C => if U≠i ∧ active L U i=true then 1 else 0
  have point (i : Id C) : ThresholdSharedFlow.budget L U i ≤
      (if i=U then fan L U else 0) + (if i∈H then hot i else 0) +
      (if i∈H.erase U then fan L i-2 else 0) +
      (if L.op i=.and then fan L i-2 else 0) := by
    by_cases e : i=U
    · subst i; cases a : active L U U <;> simp [ThresholdSharedFlow.budget,a,hot]
    · by_cases mem : i∈H
      · have geo := (hub_iff L i).mp mem
        cases a : active L U i <;> simp [ThresholdSharedFlow.budget,e,Ne.symm e,mem,geo.2,hot,a] <;> omega
      · have bad : ¬(2≤fan L i ∧ L.op i=.or) := fun h => mem ((hub_iff L i).mpr h)
        cases a : active L U i <;> cases op : L.op i <;> simp [ThresholdSharedFlow.budget,e,mem,a,op] <;> simp_all <;> omega
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => point i)
  simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Finset.sum_ite_mem,Finset.univ_inter,usable,hot,H] using sum

theorem boundary_tight (per : ∀ u∈hubs C n, (singleAt L u).card ≤ 1+max (fan L u) (leak L u)) :
    (∑ u∈hubs C n, (singleAt L u).card) ≤ 3*(hubs C n).card+deltaO L+
      (hotPairs L).card+((hubs C n).card-1)*deltaO L+(hubs C n).card*usable L := by
  let H := hubs C n
  let hot := fun (u i : Id C) => if u≠i ∧ active L u i=true then 1 else 0
  have point (u : Id C) (hu : u∈H) : (singleAt L u).card ≤
      (1+fan L u)+(∑ i∈H,hot u i)+(∑ i∈H.erase u,(fan L i-2))+usable L := by
    have p := (probe_flow L u).trans (row_tight L u hu)
    have q := per u hu
    dsimp [H,hot] at *
    omega
  have hotTotal : (∑ u∈H, ∑ i∈H, hot u i)=(hotPairs L).card := by
    rw [hotPairs,Finset.card_filter,Finset.sum_product]
  have base : (∑ u∈H, (1+fan L u))=3*H.card+deltaO L := by
    have p (u : Id C) (hu : u∈H) : 1+fan L u=3+(fan L u-2) := by
      have := ((hub_iff L u).mp hu).1; omega
    rw [Finset.sum_congr rfl p,Finset.sum_add_distrib]
    simp [deltaO,H,Nat.mul_comm]
  have extra : (∑ u∈H, ∑ i∈H.erase u, (fan L i-2))=(H.card-1)*deltaO L := by
    have t (u : Id C) : (∑ i∈H.erase u, (fan L i-2)) =
        ∑ i∈H, if i≠u then fan L i-2 else 0 := by rw [←Finset.sum_filter]; congr 1; ext; simp [and_comm]
    simp_rw [t]
    change _ = (H.card-1)*(∑ i∈H, (fan L i-2))
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [←Finset.sum_filter]
    have eq : H.filter (fun u => i≠u)=H.erase i := by ext u; simp [ne_comm,and_comm]
    simp [eq,Finset.card_erase_of_mem hi]
  have total := Finset.sum_le_sum point
  simpa only [Finset.sum_add_distrib,base,hotTotal,extra,Finset.sum_const,smul_eq_mul,H] using total
theorem regular_credit {n out : Nat} {gs : List Raw} (hn : 5≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    2*((q L:ℤ)+(hubs C n).card*(sharedAnd L:ℤ))≤ThresholdHubFine.budget n C.size := by
  intro C L
  let H := hubs C n
  let b := ∑ u∈H,(singleAt L u).card
  let p := (hotPairs L).card
  let m := (internal L).card
  let e := (missed L).card
  let d := deltaO L+usable L
  have simple := classified_simple (by omega : 2≤n) minim reg
  have st := ThresholdSharpEndpoint.structure_of_star ThresholdStarBypass.regular_star_boundary n hn gs out minim reg
  have pairs : p+m≤H.card.choose 2 := pair_budget L simple.1 simple.2.1 st.no_shared_raw
  have cap : m≤H.card.choose 2 := by omega
  have eqM : M L+m=H.card.choose 2 := Nat.sub_add_cancel cap
  have eqq : q L+p=M L := Nat.sub_add_cancel (by omega)
  have part : n=e+m+b := partition L
  have avoid : e≤4 := st.missed_bound
  have finance : deltaO L+deltaA L+H.card+2*n≤C.size+1 := by
    simpa only [d,H,deltaO,deltaA,fan_readers,ThresholdSharedFunding.extrasOr,
      ThresholdSharedFunding.extrasAnd,ThresholdSharedFunding.fan] using ThresholdSharedFunding.funding minim reg
  have orig := boundary_tight L st.leaf_bound
  have priv : b≤3*H.card+p+H.card*d := by
    by_cases pos : H.card=0
    · have empty := Finset.card_eq_zero.mp pos
      simp [b,empty]
    · have step : H.card-1+1=H.card := by omega
      have times := congrArg (fun k => k*deltaO L) step
      change b≤3*H.card+deltaO L+p+(H.card-1)*deltaO L+H.card*usable L at orig
      dsimp only [d]
      rw [Nat.add_mul] at times
      rw [Nat.mul_add]
      omega
  have choose := ThresholdSharpArithmetic.twice_choose_two H.card
  have split := decompose L
  have paid : (d:ℤ)+(sharedAnd L:ℤ)+(H.card:ℤ)≤(C.size:ℤ)-2*(n:ℤ)+1 := by
    dsimp only [d]; omega
  let s := (C.size:ℤ)-2*(n:ℤ)
  have room : 0≤s+1-(H.card:ℤ) := by dsimp only [s]; omega
  have step := mul_le_mul_of_nonneg_left (show (d:ℤ)+(sharedAnd L:ℤ)≤s+1-(H.card:ℤ) by dsimp only [s]; omega) (Int.natCast_nonneg H.card)
  have gap := mul_nonneg room (show 0≤s+6-(H.card:ℤ) by omega)
  change 2*((q L:ℤ)+(H.card:ℤ)*(sharedAnd L:ℤ))≤s^2+7*s+14-2*(n:ℤ)
  zify at priv eqM eqq part avoid
  nlinarith only [priv,eqM,eqq,part,avoid,choose,step,gap]
#print axioms regular_credit
end ThresholdSharedAndCredit
