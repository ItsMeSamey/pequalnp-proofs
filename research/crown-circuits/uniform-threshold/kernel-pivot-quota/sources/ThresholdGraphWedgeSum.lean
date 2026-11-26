import ThresholdEffectiveMatchingRows
namespace ThresholdGraphWedgeSum
open ThresholdCodegreeRecords ThresholdFourSetOccupancy
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def markedPairs (flag : Bool) : Finset (Finset V) := by
  classical exact (Finset.univ.powersetCard 2).filter (fun p => flag=true → clean G p)

open Classical in
noncomputable def by_first (flag : Bool) :
    {z : CodegreeChoice G // flag=true → clean G z.1.val} ≃
    (Σ p : ↥(markedPairs G flag), ↥((neighbors G p.val).powersetCard 2)) where
  toFun z := ⟨⟨z.val.1.val,Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _,z.val.1.property⟩,z.property⟩⟩,z.val.2⟩
  invFun z := ⟨⟨⟨z.1.val,(Finset.mem_powersetCard.mp (Finset.mem_filter.mp z.1.property).1).2⟩,
    z.2⟩,(Finset.mem_filter.mp z.1.property).2⟩
  left_inv := by rintro ⟨⟨⟨p,hp⟩,⟨r,hr⟩⟩,ok⟩; rfl
  right_inv := by rintro ⟨⟨p,hp⟩,⟨r,hr⟩⟩; rfl

theorem wedge_sum (flag : Bool)
    (chart : (F : {F : Finset V // F.card=4}) → Fin 4 ≃ ↥F.val) :
    (∑ p∈markedPairs G flag,(neighbors G p).card.choose 2)=
    ∑ F : {F : Finset V // F.card=4},
      let x := ofGraph G (chart F 0).val (chart F 1).val (chart F 2).val (chart F 3).val
      if flag then nonedge x else diagonals x := by
  classical
  let e := by_first G flag
  letI := Fintype.ofEquiv _ e.symm
  rw [←global_count G flag chart,Fintype.card_congr e,Fintype.card_sigma]
  simp only [Fintype.card_coe,Finset.card_powersetCard]
  exact (Finset.sum_attach (markedPairs G flag) (fun p => (neighbors G p).card.choose 2)).symm

end ThresholdGraphWedgeSum
