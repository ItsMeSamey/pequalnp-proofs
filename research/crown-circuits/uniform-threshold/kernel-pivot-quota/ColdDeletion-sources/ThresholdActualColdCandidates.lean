import ThresholdPhysicalColdLoss
import ThresholdEffectiveMatchingRows

namespace ThresholdActualColdCandidates
open PEqualNP.CircuitLowerBounds ResidualSurplus T2OrPartition T2SoleOrSplice T2CubeDeletion T2RegularOrDelete ThresholdOrExtraction ThresholdSimpleIncidence
open ThresholdEffectiveColumns
variable {C : Circuit} {n : Nat} (L : Layout C n) (M : LexMinimum n C)
noncomputable def box (p : Finset (Id C)) := p.biUnion (effective L M)
noncomputable def missing (R : Finset (Id C)) := R.powersetCard 2 \ ThresholdEffectiveMatchingRows.actualPool L R
def Failed (p : Finset (Id C)) (a : Id C) : Prop :=
  a∈p ∧ ∃ (x : Fin n), endpoints L x=p ∧ ∃ v∈effective L M a,
    (C.wires (vector {x})).getD (n+v.val) false=false
noncomputable def competing (R : Finset (Id C)) := by
  classical exact (R.powersetCard 2).filter (fun p =>
    (box L M p).card=4 ∧ ∃ q∈ThresholdEffectiveMatchingRows.fiber R (effective L M) (box L M p), q≠p)
noncomputable def cold (R : Finset (Id C)) := by
  classical exact (competing L M R).filter (fun p => ∃ a, Failed L M p a)

theorem orient {R : Finset (Id C)} {p} (mem : p∈cold L M R) :
    ∃ a b, p={a,b} ∧ a≠b ∧ Failed L M p a ∧ a∈R ∧ b∈R := by
  classical
  obtain ⟨comp,a,ha⟩ := Finset.mem_filter.mp mem
  obtain ⟨sub,size⟩ := Finset.mem_powersetCard.mp (Finset.mem_filter.mp comp).1
  obtain ⟨i,j,ij,eq⟩ := Finset.card_eq_two.mp size
  have h : a=i ∨ a=j := by simpa [eq] using ha.1
  rcases h with rfl|rfl
  · exact ⟨a,j,eq,ij,ha,sub (by simp [eq]),sub (by simp [eq])⟩
  · exact ⟨a,i,eq.trans (Finset.pair_comm _ _),ij.symm,ha,sub (by simp [eq]),sub (by simp [eq])⟩

noncomputable def first (R : Finset (Id C)) (p : Finset (Id C)) (fallback : Id C) := by
  classical exact if h : p∈cold L M R then (orient L M h).choose else fallback
noncomputable def second (R : Finset (Id C)) (p : Finset (Id C)) (fallback : Id C) := by
  classical exact if h : p∈cold L M R then (orient L M h).choose_spec.choose else fallback
theorem oriented {R : Finset (Id C)} {p} (fallback : Id C) (mem : p∈cold L M R) :
    let a := first L M R p fallback
    let b := second L M R p fallback
    p={a,b} ∧ a≠b ∧ Failed L M p a ∧ a∈R ∧ b∈R := by
  simpa only [first,second,dif_pos mem] using (orient L M mem).choose_spec.choose_spec

theorem competitors {R : Finset (Id C)} {p} (mem : p∈cold L M R) :
    ∃ q∈R.powersetCard 2, q≠p ∧ box L M q=box L M p := by
  classical
  obtain ⟨q,hq,ne⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp mem).1).2.2
  exact ⟨q,(Finset.mem_filter.mp hq).1,ne,(Finset.mem_filter.mp hq).2⟩

theorem actual_hot {R : Finset (Id C)} {p} (mem : p∈competing L M R)
    (real : p∉missing L R) (warm : p∉cold L M R) :
    ∃ x : Fin n,endpoints L x=p ∧ ∀ v∈box L M p,ThresholdWarmSimple.lit (C:=C) x v := by
  classical
  have pair := (Finset.mem_filter.mp mem).1
  have act : p∈ThresholdEffectiveMatchingRows.actualPool L R := by
    by_contra no
    exact real (Finset.mem_sdiff.mpr ⟨pair,no⟩)
  obtain ⟨_,_,x,raw⟩ := (ThresholdEffectiveMatchingRows.actual_iff L R p).mp act
  refine ⟨x,raw,?_⟩
  intro v hv
  obtain ⟨a,ha,hm⟩ := Finset.mem_biUnion.mp hv
  unfold ThresholdWarmSimple.lit
  cases eq : (C.wires (vector {x})).getD (n+v.val) false with
  | true => rfl
  | false => exact False.elim (warm (Finset.mem_filter.mpr ⟨mem,a,ha,x,raw,v,hm,eq⟩))

theorem missing_mono {R H : Finset (Id C)} (sub : R⊆H) : missing L R⊆missing L H := by
  intro p hp
  obtain ⟨sz,no⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨r,card⟩ := Finset.mem_powersetCard.mp sz
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨r.trans sub,card⟩,?_⟩
  intro act
  obtain ⟨_,_,raw⟩ := (ThresholdEffectiveMatchingRows.actual_iff L H p).mp act
  exact no ((ThresholdEffectiveMatchingRows.actual_iff L R p).mpr ⟨r,card,raw⟩)

/-- Deleting all singly occupied boxes does not alter the matching loss. -/
theorem box_deficiency {R : Finset (Id C)} {F : Finset (Id C)} (four : F.card=4) :
    (ThresholdColdMatchingLoss.fiber (competing L M R) (box L M) F).card - 1 =
    (ThresholdEffectiveMatchingRows.fiber R (effective L M) F).card - 1 := by
  classical
  let full := ThresholdEffectiveMatchingRows.fiber R (effective L M) F
  let kept := ThresholdColdMatchingLoss.fiber (competing L M R) (box L M) F
  change kept.card-1=full.card-1
  have sub : kept⊆full := by
    intro p hp
    obtain ⟨mem,hb⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp mem).1,hb⟩
  by_cases large : 1<full.card
  · have rev : full⊆kept := by
      intro p hp
      obtain ⟨u,hu,v,hv,uv⟩ := Finset.one_lt_card.mp large
      have other : ∃ q∈full,q≠p := by
        by_cases h : u=p
        · exact ⟨v,hv,by simpa [←h] using uv.symm⟩
        · exact ⟨u,hu,h⟩
      obtain ⟨q,hq,ne⟩ := other
      obtain ⟨pair,hb⟩ := Finset.mem_filter.mp hp
      have eq : box L M p=F := hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨pair,by rw [eq]; exact four,
        q,by simpa only [eq] using hq,ne⟩,eq⟩
    rw [Finset.Subset.antisymm sub rev]
  · have le := Finset.card_le_card sub
    omega

end ThresholdActualColdCandidates
