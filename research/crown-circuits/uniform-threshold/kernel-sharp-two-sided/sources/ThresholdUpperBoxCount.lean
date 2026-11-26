import ThresholdUpperPairCover
namespace ThresholdUpperCatalogue
open scoped BigOperators
variable {V : Type*} [LinearOrder V]

noncomputable def liveNames (R : Finset (Finset V)) (Q : Finset V) :=
  (opposites Q).filter (fun d => matching Q d⊆R)
noncomputable def boxes (U : Finset V) (R : Finset (Finset V)) :=
  (U.powersetCard 4).filter (fun Q => (liveNames R Q).Nonempty)

theorem box_count (U : Finset V) (R : Finset (Finset V)) (sub : R⊆edgeUniverse U) :
    R.card.choose 2 ≤ (boxes U R).card+
      ((stars U 2).filter (fun s => star s⊆R)).card+
      ((cycles U).filter (fun i => cycle i⊆R)).card := by
  classical
  let W := (stars U 2).filter (fun s => star s⊆R)
  let P := (U.powersetCard 4).sigma (liveNames R)
  let K := fun Q : Finset V => (opposites Q).filter (fun d => cycle (⟨Q,d⟩ : CycleName V)⊆R)
  have cover : R.powersetCard 2⊆W.image star ∪ P.image (fun s => matching s.1 s.2) := by
    intro e he
    have er := (Finset.mem_powersetCard.mp he).1
    rcases pair_cover U R sub e he with ⟨s,hs,eq⟩|⟨Q,hQ,d,hd,eq⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨hs,eq.symm ▸ er⟩,eq⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨⟨Q,d⟩,Finset.mem_sigma.mpr ⟨hQ,Finset.mem_filter.mpr ⟨hd,eq.symm ▸ er⟩⟩,eq⟩)
  have count := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have w := Finset.card_image_le (s:=W) (f:=star)
  have p := Finset.card_image_le (s:=P) (f:=fun s => matching s.1 s.2)
  have cyc : ((cycles U).filter (fun i => cycle i⊆R))=(U.powersetCard 4).sigma K := by
    ext ⟨Q,d⟩
    simp [cycles,K,and_assoc]
  have localCount (Q : Finset V) (hq : Q∈U.powersetCard 4) :
      (liveNames R Q).card≤(if (liveNames R Q).Nonempty then 1 else 0)+(K Q).card := by
    by_cases any : (liveNames R Q).Nonempty
    · rw [if_pos any]
      exact four_loss Q (Finset.mem_powersetCard.mp hq).2 R
    · simp [Finset.not_nonempty_iff_eq_empty.mp any]
  have total := Finset.sum_le_sum localCount
  have total' : P.card≤(boxes U R).card+((cycles U).filter (fun i => cycle i⊆R)).card := by
    simpa [P,boxes,cyc,Finset.card_sigma,Finset.sum_add_distrib] using total
  rw [Finset.card_powersetCard] at count
  change _ ≤ _ + W.card + _
  omega
end ThresholdUpperCatalogue
