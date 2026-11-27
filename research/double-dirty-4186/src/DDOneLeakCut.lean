import DDRegionClauses

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4186_aux Q0.Factor S4183.S98

variable {n : ℕ} {C : Circuit}

private theorem operand_mem (ao : IsAO2 n C) {j : ℕ} (hj : j<C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  obtain ⟨_,a,d,ins,_,_⟩ := AO_of_IsAO2 n C ao j hj
  fin_cases b <;> simp [opnd,ins]

private theorem closed_pin (ao : IsAO2 n C) {r i j : ℕ}
    (jr : j ∈ andRegion n C r) (hi : i<C.gates.length) (ai : (gateAt C i).op=.and)
    (b : Fin 2) (eq : opnd C j b=n+i) : i ∈ andRegion n C r := by
  obtain ⟨jb, aj, tail⟩ := in_region.mp jr
  exact in_region.mpr ⟨hi,ai,extend_and_path
    (show AndPath n C i (n+j) from .step .source jb aj (eq ▸ operand_mem ao jb b)) tail⟩

private theorem transfer_leaf (ao : IsAO2 n C) {r t : ℕ} {p : ℕ × Fin 2}
    (leaf : p ∈ leaves n C r) (dest : p.1 ∈ andRegion n C t) : p ∈ leaves n C t := by
  have pinsR := (Finset.mem_sdiff.mp leaf).1
  have ownerR := (Finset.mem_product.mp pinsR).1
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_product.mpr ⟨dest,Finset.mem_univ _⟩,?_⟩
  intro inner
  obtain ⟨k,hk,eq⟩ := (Finset.mem_filter.mp inner).2
  have ki := in_region.mp hk
  have kin := closed_pin ao ownerR ki.1 ki.2.1 p.2 eq
  exact (Finset.mem_sdiff.mp leaf).2 (Finset.mem_filter.mpr ⟨pinsR,k,kin,eq⟩)

/-- A nonempty common gate region contributes at least two common physical pin
occurrences even when it has several maximal gates. -/
theorem two_shared (ao : IsAO2 n C) {a y : ℕ}
    (share : ((andRegion n C a) ∩ andRegion n C y).Nonempty) :
    2 ≤ ((leaves n C a) ∩ leaves n C y).card := by
  classical
  let J := andRegion n C a ∩ andRegion n C y
  let j := J.min' share
  have hj : j ∈ J := Finset.min'_mem _ _
  obtain ⟨ja,jy⟩ := Finset.mem_inter.mp hj
  have leavesA (b : Fin 2) : (j,b) ∈ leaves n C a := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_product.mpr ⟨ja,Finset.mem_univ _⟩,?_⟩
    intro inner
    obtain ⟨k,ka,eq⟩ := (Finset.mem_filter.mp inner).2
    change opnd C j b = n+k at eq
    have ki := in_region.mp ka
    have ky := closed_pin ao jy ki.1 ki.2.1 b eq
    have kj : k ∈ J := Finset.mem_inter.mpr ⟨ka,ky⟩
    have lo : j ≤ k := Finset.min'_le J k kj
    have earlier := ao.2.1 j (in_region.mp ja).1 _ (operand_mem ao (in_region.mp ja).1 b)
    omega
  have sub : ({(j,0),(j,1)} : Finset (ℕ × Fin 2)) ⊆ leaves n C a ∩ leaves n C y := by
    intro p hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨leavesA 0,transfer_leaf ao (leavesA 0) jy⟩
    · exact Finset.mem_inter.mpr ⟨leavesA 1,transfer_leaf ao (leavesA 1) jy⟩
  simpa using Finset.card_le_card sub

/-- The full arm already pays for all common primitive occurrences. In the external
region, a pin reading a maximal shared ancestor supplies one unused boundary slot.
No uniqueness or connectivity assumption is required for the overlap. -/
theorem private_width (ao : IsAO2 n C) {a y : ℕ}
    (hy : y ∈ andRegion n C y) (notArm : y ∉ andRegion n C a)
    (share : ((andRegion n C a) ∩ andRegion n C y).Nonempty) :
    (leaves n C y \ leaves n C a).card ≤ (andRegion n C y \ andRegion n C a).card := by
  classical
  let A := andRegion n C a
  let Y := andRegion n C y
  let J := A ∩ Y
  let U := Y \ A
  let g := J.max' share
  have gj : g ∈ J := Finset.max'_mem _ _
  obtain ⟨ga,gy⟩ := Finset.mem_inter.mp gj
  have ne : g ≠ y := fun eq => notArm (eq ▸ ga)
  obtain ⟨cut,hpin,wcut⟩ := region_used ao y g (Finset.mem_erase.mpr ⟨ne,gy⟩)
  have cy : cut.1 ∈ Y := (Finset.mem_product.mp hpin).1
  have earlier := ao.2.1 cut.1 (in_region.mp cy).1 _ (operand_mem ao (in_region.mp cy).1 cut.2)
  have ca : cut.1 ∉ A := by
    intro inc
    have maxBound : cut.1 ≤ g := Finset.le_max' J _ (Finset.mem_inter.mpr ⟨inc,cy⟩)
    omega
  have uc : cut ∈ pins U := Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨cy,ca⟩, Finset.mem_univ _⟩
  have cutBoundary : cut ∈ occurrences n C U := by
    apply Finset.mem_sdiff.mpr
    refine ⟨uc,?_⟩
    intro h
    obtain ⟨i,hi,eq⟩ := (Finset.mem_filter.mp h).2
    have eq' : i = g := by omega
    exact (Finset.mem_sdiff.mp hi).2 (eq' ▸ ga)
  have cutInternal : cut ∈ internal n C Y := Finset.mem_filter.mpr ⟨hpin,g,gy,wcut⟩
  have sub : leaves n C y \ leaves n C a ⊆ (occurrences n C U).erase cut := by
    intro p hp
    obtain ⟨py,pna⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨yp,notInt⟩ := Finset.mem_sdiff.mp py
    have jy : p.1 ∈ Y := (Finset.mem_product.mp yp).1
    have ja : p.1 ∉ A := by
      intro ja
      exact pna (transfer_leaf ao py ja)
    refine Finset.mem_erase.mpr ⟨fun eq => notInt (eq ▸ cutInternal),?_⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨jy,ja⟩,Finset.mem_univ _⟩,?_⟩
    intro int
    obtain ⟨k,hk,eq⟩ := (Finset.mem_filter.mp int).2
    exact notInt (Finset.mem_filter.mpr ⟨yp,k,(Finset.mem_sdiff.mp hk).1,eq⟩)
  have usage : ∀ j ∈ U.erase y, ∃ p ∈ pins U, opnd C p.1 p.2 = n+j := by
    intro j hj
    obtain ⟨neq, mem⟩ := Finset.mem_erase.mp hj
    obtain ⟨jy, ja⟩ := Finset.mem_sdiff.mp mem
    obtain ⟨p,hp,eq⟩ := region_used ao y j (Finset.mem_erase.mpr ⟨neq,jy⟩)
    have own : p.1 ∈ Y := (Finset.mem_product.mp hp).1
    have ji := in_region.mp jy
    have out : p.1 ∉ A := fun parent => ja (closed_pin ao parent ji.1 ji.2.1 p.2 eq)
    exact ⟨p, Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨own,out⟩,Finset.mem_univ _⟩,eq⟩
  have bound := occurrence_bound n C U y (Finset.mem_sdiff.mpr ⟨hy,notArm⟩) usage
  have hc := Finset.card_erase_add_one cutBoundary
  have hl := Finset.card_le_card sub
  change _ ≤ U.card
  omega

/-- A single external root can overlap the retained first arm at any number of
gates. Only gates in the original circuit's four-region union are charged. -/
theorem merged_price (ao : IsAO2 n C) {a b H y : ℕ}
    (ra : a ∈ andRegion n C a) (rb : b ∈ andRegion n C b)
    (rh : H ∈ andRegion n C H) (ry : y ∈ andRegion n C y)
    (mPin : ℕ × Fin 2) (hm : mPin ∈ leaves n C H)
    (notArm : y ∉ andRegion n C a)
    (share : ((andRegion n C a) ∩ andRegion n C y).Nonempty)
    (ab : Disjoint (andRegion n C a) (andRegion n C b))
    (guardArms : Disjoint (andRegion n C a ∪ andRegion n C b) ((andRegion n C H).erase H))
    (bExt : Disjoint (andRegion n C b) (andRegion n C y))
    (guardExt : Disjoint ((andRegion n C H).erase H) (andRegion n C y)) :
    (leaves n C a).card + (leaves n C b).card + ((leaves n C H).erase mPin).card +
        (leaves n C y \ leaves n C a).card + 1 ≤
      (andRegion n C a ∪ andRegion n C b ∪ (andRegion n C H).erase H ∪
        (andRegion n C y).erase y).card + 2 * 2 + 1 := by
  classical
  let A := andRegion n C a
  let B := andRegion n C b
  let W := (andRegion n C H).erase H
  let Y := andRegion n C y
  let E := (Y \ A).erase y
  have dis : Disjoint (A ∪ B ∪ W) E := by
    apply Finset.disjoint_left.mpr
    intro i hold he
    obtain ⟨_, hi⟩ := Finset.mem_erase.mp he
    obtain ⟨iy, ia⟩ := Finset.mem_sdiff.mp hi
    rcases Finset.mem_union.mp hold with hab | iw
    · rcases Finset.mem_union.mp hab with ha | hb
      · exact ia ha
      · exact Finset.disjoint_left.mp bExt hb iy
    · exact Finset.disjoint_left.mp guardExt iw iy
  have covered : A ∪ B ∪ W ∪ E ⊆ A ∪ B ∪ W ∪ Y.erase y := by
    intro i hi
    rcases Finset.mem_union.mp hi with hold | he
    · exact Finset.mem_union_left _ hold
    · obtain ⟨ne,hi⟩ := Finset.mem_erase.mp he
      exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,(Finset.mem_sdiff.mp hi).1⟩)
  have hc := Finset.card_le_card covered
  rw [Finset.card_union_of_disjoint dis, Finset.card_union_of_disjoint guardArms,
    Finset.card_union_of_disjoint ab] at hc
  change A.card + B.card + W.card + E.card ≤ (A ∪ B ∪ W ∪ Y.erase y).card at hc
  have pa : (leaves n C a).card ≤ A.card+1 := occurrence_bound n C A a ra (region_used ao a)
  have pb : (leaves n C b).card ≤ B.card+1 := occurrence_bound n C B b rb (region_used ao b)
  have pw : ((leaves n C H).erase mPin).card ≤ W.card+1 :=
    guard_occurrences n C _ H rh (region_used ao H) mPin hm
  have pe : (leaves n C y \ leaves n C a).card ≤ (Y\A).card := private_width ao ry notArm share
  have one : E.card+1 = (Y\A).card := Finset.card_erase_add_one (Finset.mem_sdiff.mpr ⟨ry,notArm⟩)
  change _ ≤ (A ∪ B ∪ W ∪ Y.erase y).card + 2 * 2 + 1
  omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak
