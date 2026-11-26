import ThresholdUpperCollisionMass
namespace ThresholdUpperFailedMass
open ThresholdUpperSecond ThresholdUpperExtension ThresholdUpperEventGeometry
open Classical
/-- An edge intersecting a distinct old edge has one old endpoint and one
outside endpoint, hence at most 2(z−2) allowed choices. -/
theorem adjacent_card {z} (a : Edges z) :
    (Finset.univ.filter (fun b : Edges z => b≠a ∧ ¬Disjoint b.val a.val)).card≤2*(z-2) := by
  classical
  let D := Finset.univ.filter (fun b : Edges z => b≠a ∧ ¬Disjoint b.val a.val)
  let P := a.val.product (Finset.univ \ a.val)
  let make := fun p : Fin z×Fin z => ({p.1,p.2}:Finset (Fin z))
  have sub : D.image Subtype.val⊆P.image make := by
    intro e he
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨ne,meet⟩ := (Finset.mem_filter.mp hb).2
    obtain ⟨x,xb,xa⟩ := Finset.not_disjoint_iff.mp meet
    have asz := (Finset.mem_powersetCard.mp a.property).2
    have bsz := (Finset.mem_powersetCard.mp b.property).2
    have outside : ¬b.val⊆a.val := fun h => ne (Subtype.ext (Finset.eq_of_subset_of_card_le h (by omega)))
    obtain ⟨y,yb,ya⟩ := Finset.not_subset.mp outside
    have xy : x≠y := fun eq => ya (eq ▸ xa)
    refine Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr
      ⟨xa,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,ya⟩⟩,?_⟩
    apply Finset.eq_of_subset_of_card_le
    · intro q h
      rcases Finset.mem_insert.mp h with rfl|hy
      · exact xb
      · exact (Finset.mem_singleton.mp hy).symm ▸ yb
    · simp [make,bsz,xy]
  have count := (Finset.card_le_card sub).trans Finset.card_image_le
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at count
  change D.card≤_
  simpa [P,Finset.card_product,Finset.card_sdiff_of_subset (Finset.subset_univ a.val),
    (Finset.mem_powersetCard.mp a.property).2] using count

theorem bad_witness {w z} (Q : Finset (Fin w)) (four : Q.card=4) (u : Injection w z)
    (bad : failed Q u) : ∃ p∈Q.powersetCard 2, ∃ i∈p,∃ j∈p,i≠j ∧ ¬Disjoint (u i).val (u j).val := by
  classical
  by_contra! no
  have dis : (Q:Set (Fin w)).PairwiseDisjoint (fun i => (u i).val) := by
    intro i hi j hj ne
    have pair : {i,j}∈Q.powersetCard 2 := Finset.mem_powersetCard.mpr
      ⟨by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl|hh
        · exact hi
        · exact (Finset.mem_singleton.mp hh).symm ▸ hj,by simp [ne]⟩
    exact no _ pair i (by simp) j (by simp) ne
  apply bad
  change (Q.biUnion (fun i => (u i).val)).card=8
  rw [Finset.card_biUnion dis]
  simp [edge_two,four]

theorem fixed_pair {w z} (p : Finset (Fin w)) (two : p.card=2) :
    (Finset.univ.filter (fun u : Injection w z =>
      ∃ i∈p,∃ j∈p,i≠j ∧ ¬Disjoint (u i).val (u j).val)).card ≤
       Fintype.card (Edges z)*(2*(z-2))*
         (Fintype.card (Edges z)-2).descFactorial (w-2) := by
  classical
  obtain ⟨a,b,ne,eq⟩ := Finset.card_eq_two.mp two
  let A : ↥p := ⟨a,by simp [eq]⟩
  let B : ↥p := ⟨b,by simp [eq]⟩
  let bad := Finset.univ.filter (fun f : ↥p ↪ Edges z => ¬Disjoint (f A).val (f B).val)
  let buckets := fun x : Edges z => Finset.univ.filter (fun y => y≠x ∧ ¬Disjoint y.val x.val)
  have sub : bad.card≤(Finset.univ.sigma buckets).card := by
    apply Finset.card_le_card_of_injOn (fun f => ⟨f A,f B⟩)
    · intro f hf
      have neq : B≠A := fun h => ne (congrArg Subtype.val h).symm
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        f.injective.ne neq,fun h => (Finset.mem_filter.mp hf).2 h.symm⟩⟩
    · intro f _ g _ h
      apply DFunLike.ext
      intro x
      have xx : x.val=a ∨ x.val=b := by simpa [eq] using x.property
      rcases xx with ha|hb
      · have same : x=A := Subtype.ext ha
        exact same ▸ congrArg Sigma.fst h
      · have same : x=B := Subtype.ext hb
        exact same ▸ congrArg (fun t : Σ _ : Edges z, Edges z => t.2) h
  rw [Finset.card_sigma] at sub
  have cap : bad.card≤Fintype.card (Edges z)*(2*(z-2)) := by
    have all := Finset.sum_le_sum (s:=Finset.univ) (fun (x : Edges z) _ => adjacent_card x)
    exact sub.trans (by simpa [buckets] using all)
  let s := ThresholdUpperCollisionMass.firstSplit p
  let D := Finset.univ.filter (fun u : Injection w z => (splitInj s u).1∈bad)
  have inc : (Finset.univ.filter (fun u : Injection w z =>
      ∃ i∈p,∃ j∈p,i≠j ∧ ¬Disjoint (u i).val (u j).val))⊆D := by
    intro u hu
    obtain ⟨i,hi,j,hj,ij,meet⟩ := (Finset.mem_filter.mp hu).2
    have hi' : i=a ∨ i=b := by simpa [eq] using hi
    have hj' : j=a ∨ j=b := by simpa [eq] using hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    change ¬Disjoint (u a).val (u b).val
    rcases hi' with rfl|rfl <;> rcases hj' with rfl|rfl <;> simp_all [disjoint_comm]
  have exactD := full_count s bad
  have cnt := Fintype.card_of_subtype D (p:=fun u => (splitInj s u).1∈bad) (by intro u; simp [D])
  apply (Finset.card_le_card inc).trans
  rw [←cnt,exactD]
  simp only [Fintype.card_coe,two,ThresholdUpperCollisionMass.Out,Fintype.card_subtype_compl,
    Fintype.card_fin]
  simp only [Edges,Fintype.card_coe] at cap
  exact Nat.mul_le_mul_right _ cap

theorem failed_mass {w z} (Q : Finset (Fin w)) (four : Q.card=4) :
    (Finset.univ.filter (failed (z:=z) Q)).card ≤
      6*(Fintype.card (Edges z)*(2*(z-2))*(Fintype.card (Edges z)-2).descFactorial (w-2)) := by
  classical
  let K := fun p : Finset (Fin w) => Finset.univ.filter (fun u : Injection w z =>
    ∃ i∈p,∃ j∈p,i≠j ∧ ¬Disjoint (u i).val (u j).val)
  have incl : (Finset.univ.filter (failed (z:=z) Q))⊆(Q.powersetCard 2).biUnion K := by
    intro u hu
    obtain ⟨p,hp,h⟩ := bad_witness Q four u (Finset.mem_filter.mp hu).2
    exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
  have cnt := (Finset.card_le_card incl).trans Finset.card_biUnion_le
  have each := Finset.sum_le_sum (s:=Q.powersetCard 2)
    (fun p hp => fixed_pair (z:=z) p (Finset.mem_powersetCard.mp hp).2)
  exact cnt.trans (by simpa [K,Finset.card_powersetCard,four,show Nat.choose 4 2=6 by decide] using each)
end ThresholdUpperFailedMass
