import ThresholdActualColdCandidates
import ThresholdNativeSharpColumnLedger
namespace ThresholdHighMissingIdentity
open PEqualNP.CircuitLowerBounds ResidualSurplus T2OrPartition T2SoleOrSplice T2CubeDeletion T2RegularOrDelete
open ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence ThresholdHighComponents
open ThresholdSharedPartition ThresholdSharedFlow ThresholdNativeColumnCharge

theorem native {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out)) (reg : Regular n gs) :
    let L := layout n gs out M.eligible
    ThresholdActualColdCandidates.missing L (high L)=inner L (high L) := by
  classical
  intro L
  let H := high L
  have sub : H⊆hubs (source gs out) n := Finset.filter_subset _ _
  ext p
  constructor
  · intro mem
    obtain ⟨pair,no⟩ := Finset.mem_sdiff.mp mem
    obtain ⟨ss,sz⟩ := Finset.mem_powersetCard.mp pair
    obtain ⟨a,b,ne,eq⟩ := Finset.card_eq_two.mp sz
    have ha := ss (show a∈p by simp [eq])
    have hb := ss (show b∈p by simp [eq])
    have absent : ¬ThresholdWarmSimple.Edge L b a := by
      rintro ⟨_,x,raw⟩
      apply no
      exact (ThresholdEffectiveMatchingRows.actual_iff L H p).mpr
        ⟨ss,sz,x,raw.trans ((Finset.pair_comm _ _).trans eq.symm)⟩
    have anti i (hi : i∈H) j (hj : j∈H) (ij : i≠j) : active L i j≠true :=
      fun lit => ThresholdPhysicalIdeals.high_antichain M reg i hi j hj
        ((ThresholdPhysicalIdeals.mem_pair L i j).mpr ⟨⟨sub hi,sub hj⟩,ij,lit⟩)
    exact Finset.mem_filter.mpr ⟨eq.symm ▸ genuinely_free L (sub hb) (sub ha) ne.symm
      absent (anti b hb a ha ne.symm) (anti a ha b hb ne),ss⟩
  · intro mem
    obtain ⟨free,ss⟩ := Finset.mem_filter.mp mem
    obtain ⟨pair,none⟩ := Finset.mem_sdiff.mp free
    have sz := (Finset.mem_powersetCard.mp pair).2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨ss,sz⟩,?_⟩
    intro act
    obtain ⟨_,_,x,raw⟩ := (ThresholdEffectiveMatchingRows.actual_iff L H p).mp act
    have hsub : endpoints L x⊆hubs (source gs out) n := by rw [raw]; exact ss.trans sub
    have hx : x∈internal L := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,by rw [hits,Finset.inter_eq_left.mpr hsub,raw,sz]⟩
    exact none (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,raw⟩))

#print axioms native
end ThresholdHighMissingIdentity
