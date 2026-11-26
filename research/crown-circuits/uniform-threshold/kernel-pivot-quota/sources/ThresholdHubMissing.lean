import ThresholdHighComponents
import ThresholdHubBootstrap
namespace ThresholdHubMissing
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrExtraction ThresholdSimpleIncidence
open ThresholdHubDegrees ThresholdHighComponents ThresholdSharedPartition ThresholdSharedFlow ThresholdFlowPairs
open ThresholdProbeIdeals ThresholdFlowSum T2OrPartition
variable {C : Circuit} {n : Nat} (L : Layout C n)
noncomputable def M := (hubs C n).card.choose 2 - (internal L).card
noncomputable def q := M L-(hotPairs L).card

theorem low_arc_budget (B : Nat) (cuts : ∀ I,Ideal (hotPairs L) I → (Cut (hotPairs L) I).card≤B)
    (anti : Anti (hotPairs L) (high L)) :
    (hotPairs L).card≤2*B+((hubs C n) \ high L).card.choose 2 := by
  classical
  let X := (hubs C n) \ high L
  let Q := hotPairs L
  let A := Touch Q (high L)
  let F := Q \ A
  have sub : A⊆Q := Finset.filter_subset _ _
  have toPair (p) (hp : p∈F) : unordered p∈X.powersetCard 2 := by
    have hq := (Finset.mem_sdiff.mp hp).1
    obtain ⟨⟨u,v⟩,ne,on⟩ := (ThresholdPhysicalIdeals.mem_pair L p.1 p.2).mp hq
    have away : ¬(p.1∈high L ∨ p.2∈high L) := fun e =>
      (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨hq,e⟩)
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.insert_subset (Finset.mem_sdiff.mpr ⟨u,fun h => away (Or.inl h)⟩)
      (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mpr ⟨v,fun h => away (Or.inr h)⟩)),
      Finset.card_pair_eq_two_iff.mpr ne⟩
  have inj : (F : Set (Id C×Id C)).InjOn unordered := by
    intro p hp r hr eq
    have h := (ThresholdPhysicalIdeals.mem_pair L p.1 p.2).mp (Finset.mem_sdiff.mp hp).1
    have h' := (ThresholdPhysicalIdeals.mem_pair L r.1 r.2).mp (Finset.mem_sdiff.mp hr).1
    have a := oriented L h.2.1 h.2.2
    have b := oriented L h'.2.1 h'.2.2
    have f : p.1=r.1 ∨ p.1=r.2 := by
      have hit : p.1∈unordered r := eq ▸ (by simp [unordered] : p.1∈unordered p)
      simpa [unordered] using hit
    have s : p.2=r.1 ∨ p.2=r.2 := by
      have hit : p.2∈unordered r := eq ▸ (by simp [unordered] : p.2∈unordered p)
      simpa [unordered] using hit
    rcases f with f|f <;> rcases s with s|s <;> first | exact Prod.ext f s | grind
  have low : F.card≤X.card.choose 2 := by
    simpa using Finset.card_le_card_of_injOn unordered toPair inj
  have h := touch_bound Q (high L) (ThresholdPhysicalIdeals.trans L) anti B cuts
  change A.card≤2*B at h
  have partition : F.card+A.card=Q.card := Finset.card_sdiff_add_card_eq_card sub
  change Q.card≤2*B+X.card.choose 2
  omega

theorem shared_handshake (two : ∀ x,(endpoints L x).card=2)
    (inj : Function.Injective (endpoints L)) :
    (∑ i∈hubs C n,(neighbors L i).card)=2*(internal L).card := by
  have p := Finset.sum_congr (s₁:=hubs C n) rfl (fun i hi => degrees_partition L i hi two inj)
  rw [Finset.sum_add_distrib] at p
  have e := sum_degrees L two
  have full := ThresholdSharedPartition.partition L
  omega

theorem low_deficiency (two : ∀ x,(endpoints L x).card=2)
    (inj : Function.Injective (endpoints L))
    (capacity : (internal L).card≤(hubs C n).card.choose 2) :
    let h : ℤ := (hubs C n).card
    let l : ℤ := ((hubs C n) \ high L).card
    l*(h-2)≤4*(M L:ℤ) := by
  classical
  let H := hubs C n
  let A := high L
  let F := H \ A
  intro h l
  have split := Finset.sum_sdiff (s₁:=A) (s₂:=H) (f:=fun u => (neighbors L u).card)
    (Finset.filter_subset _ _)
  have csplit := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ H : A⊆H)
  have ah (u) (hu : u∈A) : (neighbors L u).card+1≤H.card := by
    have mem : u∈H := (Finset.mem_filter.mp hu).1
    have subset : neighbors L u ⊆ H.erase u := fun v hv =>
      Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hv).2.1,(Finset.mem_filter.mp hv).1⟩
    have le := Finset.card_le_card subset
    rw [Finset.card_erase_of_mem mem] at le
    have pos : 0<H.card := Finset.card_pos.mpr ⟨u,mem⟩
    omega
  have fl (u) (hu : u∈F) : 2*(neighbors L u).card≤H.card := by
    have z := Finset.mem_sdiff.mp hu
    by_contra! gt
    exact z.2 (Finset.mem_filter.mpr ⟨z.1,gt⟩)
  have pa := Finset.sum_le_sum ah
  have pf := Finset.sum_le_sum fl
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,Nat.mul_one,←Finset.mul_sum] at pa pf
  have hand := shared_handshake L two inj
  have choose := ThresholdSharpArithmetic.twice_choose_two H.card
  have span : M L+(internal L).card=H.card.choose 2 := Nat.sub_add_cancel capacity
  change (∑ i∈F,(neighbors L i).card)+(∑ i∈A,(neighbors L i).card)=∑ i∈H,(neighbors L i).card at split
  change F.card+A.card=H.card at csplit
  change (F.card:ℤ)*((H.card:ℤ)-2)≤4*(M L:ℤ)
  have pa' : (∑ i∈A,(neighbors L i).card:ℕ)+A.card≤A.card*H.card := pa
  have pf' : 2*(∑ i∈F,(neighbors L i).card:ℕ)≤F.card*H.card := pf
  zify at pa' pf' split csplit hand span
  nlinarith only [pa',pf',split,csplit,hand,span,choose,
    congrArg (fun x : ℤ => x*(H.card:ℤ)) csplit]
#print axioms low_deficiency
#print axioms low_arc_budget
end ThresholdHubMissing
