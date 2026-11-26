import ThresholdUpperBoxCount
import ThresholdC4
namespace ThresholdUpperOverlapTwo
open ThresholdUpperCatalogue
variable {V : Type*} [LinearOrder V]
def incident (R : Finset (Finset V)) (a : V) := R.filter (fun e => a∈e)
def through (F : Finset (Finset V)) (p : Finset V) := F.filter (fun Q => p⊆Q)
noncomputable def overlapTwo (F : Finset (Finset V)) := by
  classical exact (F.powersetCard 2).filter (fun t => ∃ a b : Finset V,t={a,b} ∧ (a∩b).card=2)

theorem support_edges {U : Finset V} {R : Finset (Finset V)} {Q : Finset V}
    (hq : Q∈boxes U R) : ∃ e∈R,∃ f∈R,Q=e∪f := by
  classical
  obtain ⟨q4,d,hd⟩ := Finset.mem_filter.mp hq
  obtain ⟨opp,sub⟩ := Finset.mem_filter.mp hd
  have sz := (Finset.mem_powersetCard.mp q4).2
  have non : Q.Nonempty := Finset.card_pos.mp (by omega)
  let a := Q.min' non
  have ha : a∈Q := Q.min'_mem non
  have hde : d∈Q.erase a := by simpa [opposites,non,a] using opp
  have hq' := (Finset.mem_erase.mp hde).2
  let f := (Q.erase a).erase d
  have m : matching Q d={{a,d},f} := by simp [matching,anchor,a,f,non]
  refine ⟨{a,d},sub (by simp [m]),f,sub (by simp [m]),?_⟩
  ext v
  by_cases va : v=a <;> by_cases vd : v=d <;> simp_all [f]

theorem pair_cap {U : Finset V} {R F : Finset (Finset V)}
    (edges : R⊆edgeUniverse U) (live : F⊆boxes U R) (Δ : Nat)
    (degree : ∀ a∈U,(incident R a).card≤Δ) {p : Finset V} (pair : p∈U.powersetCard 2) :
    (through F p).card≤R.card+Δ^2 := by
  classical
  obtain ⟨ab,sz⟩ := Finset.mem_powersetCard.mp pair
  obtain ⟨a,b,ne,eq⟩ := Finset.card_eq_two.mp sz
  let same := R.image (fun f => p∪f)
  let split := ((incident R a).product (incident R b)).image (fun z => z.1∪z.2)
  have into : through F p⊆same∪split := by
    intro Q h
    obtain ⟨hf,pp⟩ := Finset.mem_filter.mp h
    obtain ⟨e,he,f,hf',joined⟩ := support_edges (live hf)
    have psub : p⊆e∪f := joined ▸ pp
    have exactEdge (d : Finset V) (mem : d∈R) (x : a∈d) (y : b∈d) : p=d := by
      apply Finset.eq_of_subset_of_card_le
      · rw [eq]; exact Finset.insert_subset x (Finset.singleton_subset_iff.mpr y)
      · rw [sz,(Finset.mem_powersetCard.mp (edges mem)).2]
    have ea := Finset.mem_union.mp (psub (show a∈p by simp [eq]))
    have eb := Finset.mem_union.mp (psub (show b∈p by simp [eq]))
    rcases ea with ae|af <;> rcases eb with be|bf
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨f,hf',by rw [exactEdge e he ae be,joined]⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(e,f),Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨he,ae⟩,Finset.mem_filter.mpr ⟨hf',bf⟩⟩,joined.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(f,e),Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hf',af⟩,Finset.mem_filter.mpr ⟨he,be⟩⟩,
        (Finset.union_comm _ _).trans joined.symm⟩)
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e,he,by rw [exactEdge f hf' af bf,joined,Finset.union_comm]⟩)
  have v := (Finset.card_le_card into).trans (Finset.card_union_le _ _)
  have n1 : same.card≤R.card := Finset.card_image_le
  have n2 := Finset.card_image_le (s:=(incident R a).product (incident R b)) (f:=fun z => z.1∪z.2)
  change split.card≤((incident R a) ×ˢ (incident R b)).card at n2
  rw [Finset.card_product] at n2
  have d := Nat.mul_le_mul (degree a (ab (by simp [eq]))) (degree b (ab (by simp [eq])))
  rw [pow_two]
  omega

theorem total {U : Finset V} {F : Finset (Finset V)} (four : F⊆U.powersetCard 4) :
    (∑ p∈U.powersetCard 2,(through F p).card)=6*F.card := by
  classical
  let rel := fun (p Q : Finset V) => p⊆Q
  have flip := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s:=U.powersetCard 2) (t:=F) rel
  have count (Q) (hQ : Q∈F) : ((U.powersetCard 2).bipartiteBelow rel Q).card=6 := by
    have val := Finset.mem_powersetCard.mp (four hQ)
    have eq : (U.powersetCard 2).bipartiteBelow rel Q=Q.powersetCard 2 := by
      ext p
      simp only [Finset.mem_bipartiteBelow,Finset.mem_powersetCard,rel]
      exact ⟨fun h=>⟨h.2,h.1.2⟩,fun h=>⟨⟨h.1.trans val.1,h.2⟩,h.1⟩⟩
    rw [eq,Finset.card_powersetCard,val.2]; decide
  change (∑ p∈U.powersetCard 2,(F.bipartiteAbove rel p).card)=_
  rw [flip,Finset.sum_congr rfl count]
  simp [Nat.mul_comm]

theorem overlap_count {U : Finset V} {R F : Finset (Finset V)}
    (edges : R⊆edgeUniverse U) (live : F⊆boxes U R) (Δ : Nat)
    (degree : ∀ a∈U,(incident R a).card≤Δ) :
    (overlapTwo F).card≤3*F.card*(R.card+Δ^2-1) := by
  classical
  let I := U.powersetCard 2
  let d := R.card+Δ^2
  have four : F⊆U.powersetCard 4 := fun a ha => (Finset.mem_filter.mp (live ha)).1
  have cover : overlapTwo F⊆I.biUnion (fun p=>(through F p).powersetCard 2) := by
    intro t ht
    obtain ⟨pair,a,b,te,sz⟩ := Finset.mem_filter.mp ht
    obtain ⟨sub,card⟩ := Finset.mem_powersetCard.mp pair
    have af := sub (show a∈t by simp [te])
    have bf := sub (show b∈t by simp [te])
    have au := (Finset.mem_powersetCard.mp (four af)).1
    apply Finset.mem_biUnion.mpr
    refine ⟨a∩b,Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left.trans au,sz⟩,
      Finset.mem_powersetCard.mpr ⟨?_,card⟩⟩
    intro Q h
    have j : Q=a ∨ Q=b := by simpa [te] using h
    rcases j with rfl|rfl
    · exact Finset.mem_filter.mpr ⟨af,Finset.inter_subset_left⟩
    · exact Finset.mem_filter.mpr ⟨bf,Finset.inter_subset_right⟩
  have lim := (Finset.card_le_card cover).trans (Finset.card_biUnion_le)
  simp only [Finset.card_powersetCard] at lim
  have one (z : Nat) : 2*z.choose 2=z*(z-1) := by
    cases z with
    | zero => decide
    | succ k =>
      induction k with
      | zero => decide
      | succ j ih =>
        rw [Nat.choose_succ_succ]
        simp only [Nat.choose_one_right,Nat.succ_sub_one] at *
        nlinarith
  have point (p) (hp : p∈I) :
      2*(through F p).card.choose 2≤(through F p).card*(d-1) := by
    rw [one]
    exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (pair_cap edges live Δ degree hp) 1)
  have cap := Finset.sum_le_sum point
  rw [←Finset.mul_sum,←Finset.sum_mul] at cap
  have t : (∑ p∈I,(through F p).card)=6*F.card := total four
  rw [t] at cap
  change (overlapTwo F).card≤3*F.card*(d-1)
  nlinarith only [cap,lim]
#print axioms overlap_count
end ThresholdUpperOverlapTwo
