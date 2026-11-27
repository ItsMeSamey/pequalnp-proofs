import Q1DoubleTrianglePhysical
import Q1DoubleTriangleRegion
import Q1DoublePhysicalLabels
import DDRegionResources

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem finish_grouped {n H : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (D : Allocation G C) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (one : (orN G C \ lam G C).card=1) (present : D.pivot ∈ D.components)
    (paid : ∀ i ∈ D.components.erase D.pivot, D.Local i)
    (a b guard external : Finset ℕ) (ja jb : Finset ℕ) (ha : ja.Nonempty) (hb : jb.Nonempty)
    (leftSub : ja ⊆ a) (rightSub : jb ⊆ b)
    (rawLeft : occurrences n C ja ⊆ occurrences n C a) (rawRight : occurrences n C jb ⊆ occurrences n C b)
    (hg : guard.Nonempty) (m : Pin) (hm : m ∈ occurrences n C guard)
    (cuts : Finset Pin) (disAB : Disjoint a b) (disGA : Disjoint guard a) (disGB : Disjoint guard b)
    (disEA : Disjoint external a) (disEB : Disjoint external b)
    (backA : ∀ j ∈ a, ∀ k, opnd C j k < n+j)
    (backB : ∀ j ∈ b, ∀ k, opnd C j k < n+j) (backG : ∀ j ∈ guard, ∀ k, opnd C j k < n+j)
    (central outer : Finset (Sym2 (Fin n))) (disE : Disjoint central outer)
    (parts : D.edges D.pivot = central ∪ outer)
    (res : D.edges D.pivot ⊆ Ustar G C) (own : central ⊆ gammaE G C H)
    (p q e : (Fin n → Bool) → Bool) (split : ∀ x, gateVal n C H x = (p x || q x))
    (extOwn : ∀ f ∈ outer, AcceptPair e f)
    (sigP : Signal G C (occurrences n C a ∪ (occurrences n C guard).erase m) p)
    (sigQ : Signal G C (occurrences n C b ∪ (occurrences n C guard).erase m) q)
    (sigR : Signal G C (occurrences n C ja ∪
      occurrences n C jb ∪ (occurrences n C external \ cuts)) e)
    (budget : (occurrences n C a).card + (occurrences n C b).card +
      ((occurrences n C guard).erase m).card +
      (occurrences n C external \ cuts).card+2 ≤ D.allowance D.pivot+1) : Positive G C := by
  classical
  let A := occurrences n C a
  let B := occurrences n C b
  let W := (occurrences n C guard).erase m
  let K := occurrences n C ja
  let M := occurrences n C jb
  let Z := occurrences n C external \ cuts
  have ka : K ⊆ A := rawLeft
  have mb : M ⊆ B := rawRight
  have wa : Disjoint W A := (disjoint_occurrences disGA).mono_left (Finset.erase_subset _ _)
  have wb : Disjoint W B := (disjoint_occurrences disGB).mono_left (Finset.erase_subset _ _)
  have km : Disjoint K M := (disjoint_occurrences disAB).mono ka mb
  have zk : Disjoint Z K := (disjoint_occurrences disEA).mono (Finset.sdiff_subset) ka
  have zm : Disjoint Z M := (disjoint_occurrences disEB).mono (Finset.sdiff_subset) mb
  have wk := wa.mono_right ka
  have wm := wb.mono_right mb
  have hw : 1 ≤ W.card := guard_nonempty guard hg backG m hm
  have hk : 2 ≤ K.card := two_boundary ja ha (fun j hj => backA j (leftSub hj))
  have hl : 2 ≤ M.card := two_boundary jb hb (fun j hj => backB j (rightSub hj))
  obtain ⟨L,R,lr,union,_,actL,actR⟩ := partitionProjected G C central own p q split
  have cc : central ⊆ Ustar G C := fun f hf => res (parts ▸ Finset.mem_union_left _ hf)
  have sr : outer ⊆ Ustar G C := fun f hf => res (parts ▸ Finset.mem_union_right _ hf)
  have lc : L ⊆ central := fun f hf => union ▸ Finset.mem_union_left _ hf
  have rc : R ⊆ central := fun f hf => union ▸ Finset.mem_union_right _ hf
  obtain ⟨P,ep⟩ := rows_of_signal four _ p sigP L (lc.trans cc) actL
  obtain ⟨Q,eq⟩ := rows_of_signal four _ q sigQ R (rc.trans cc) actR
  obtain ⟨F,ef⟩ := rows_of_signal four _ e sigR outer sr extOwn
  have pl := enumerated_edges L P.pt L.equivFin ep
  have qr := enumerated_edges R Q.pt R.equivFin eq
  have fe := enumerated_edges outer F.pt outer.equivFin ef
  have lhs := Finset.card_sdiff_add_card_eq_card ka
  have rhs := Finset.card_sdiff_add_card_eq_card mb
  have psize : (A∪W).card = W.card+K.card+(A \ K).card := by
    rw [Finset.card_union_of_disjoint wa.symm]; omega
  have qsize : (B∪W).card = W.card+M.card+(B \ M).card := by
    rw [Finset.card_union_of_disjoint wb.symm]; omega
  have fsize : (K∪M∪Z).card = K.card+M.card+Z.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨zk.symm,zm.symm⟩),
      Finset.card_union_of_disjoint km]
  obtain ⟨V,cP,cQ,cF,price⟩ := triangle_cover (raw C) P Q F four
    Finset.subset_union_right Finset.subset_union_right
    (ka.trans Finset.subset_union_left) (Finset.subset_union_left.trans Finset.subset_union_left)
    (mb.trans Finset.subset_union_left) (Finset.subset_union_right.trans Finset.subset_union_left)
    wk wm km hw hk hl psize qsize fsize
    (exclusive_of_disjoint _ _ (by rwa [pl,qr]))
    (exclusive_of_disjoint _ _ (by rw [pl,fe]; exact disE.mono_left lc))
    (exclusive_of_disjoint _ _ (by rw [qr,fe]; exact disE.mono_left rc))
  have cL := Allocation.coversRowEdges P.pt V cP
  have cR := Allocation.coversRowEdges Q.pt V cQ
  have cE := Allocation.coversRowEdges F.pt V cF
  rw [pl] at cL
  rw [qr] at cR
  rw [fe] at cE
  apply D.finishIncremental four edge least form one present paid res
  intro T _
  refine ⟨V,?_,?_⟩
  · intro u v mem
    rw [parts,← union] at mem
    rcases Finset.mem_union.mp mem with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact (cL u v h).imp (Finset.mem_union_right T) (Finset.mem_union_right T)
      · exact (cR u v h).imp (Finset.mem_union_right T) (Finset.mem_union_right T)
    · exact (cE u v h).imp (Finset.mem_union_right T) (Finset.mem_union_right T)
  · have card := Finset.card_union_le T V
    have edgeCard := Finset.card_union_of_disjoint disE
    have centralCard := Finset.card_union_of_disjoint lr
    rw [union] at centralCard
    change V.card+L.card+R.card+outer.card ≤ W.card+K.card+M.card+(A \ K).card+(B \ M).card+Z.card+2 at price
    have vPrice : V.card + central.card + outer.card ≤ A.card+B.card+W.card+Z.card+2 := by
      rw [centralCard]
      omega
    rw [parts,edgeCard]
    exact (by omega : (T ∪ V).card + (central.card + outer.card) ≤ T.card + (A.card+B.card+W.card+Z.card+2)).trans
      (Nat.add_le_add_left budget T.card)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4186_aux

variable {n : ℕ} {C : Circuit}

def ClosedWithin (n : ℕ) (C : Circuit) (J T : Finset ℕ) :=
  ∀ j ∈ J, ∀ b i, i ∈ T → opnd C j b=n+i → i ∈ J

theorem intersection_closed (ao : IsAO2 n C) (r t : ℕ) :
    ClosedWithin n C (andRegion n C r ∩ andRegion n C t) (andRegion n C r) ∧
    ClosedWithin n C (andRegion n C r ∩ andRegion n C t) (andRegion n C t) := by
  constructor
  · intro j hj b i hi wire
    have info := in_region.mp hi
    exact Finset.mem_inter.mpr ⟨hi,region_read_closed ao (Finset.mem_inter.mp hj).2 info.1 info.2.1 b wire⟩
  · intro j hj b i hi wire
    have info := in_region.mp hi
    exact Finset.mem_inter.mpr ⟨region_read_closed ao (Finset.mem_inter.mp hj).1 info.1 info.2.1 b wire,hi⟩

theorem boundary_inclusion {J T : Finset ℕ} (sub : J ⊆ T) (closed : ClosedWithin n C J T) :
    occurrences n C J ⊆ occurrences n C T := by
  intro p hp
  obtain ⟨pin,no⟩ := Finset.mem_sdiff.mp hp
  have owner := (Finset.mem_product.mp pin).1
  have pt : p ∈ pins T := Finset.mem_product.mpr ⟨sub owner,Finset.mem_univ _⟩
  refine Finset.mem_sdiff.mpr ⟨pt,?_⟩
  intro h
  obtain ⟨j,hj,wire⟩ := (Finset.mem_filter.mp h).2
  exact no (Finset.mem_filter.mpr ⟨pin,j,closed _ owner _ _ hj wire,wire⟩)

theorem intersection_nonempty {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {a t H : ℕ}
    (label : t ∈ externalLabels G C H a) :
    (andRegion n C a ∩ andRegion n C t).Nonempty := by
  classical
  obtain ⟨i,ia,it⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp label).2
  exact ⟨i,Finset.mem_inter.mpr ⟨ia,Finset.mem_of_mem_erase it⟩⟩

theorem partition_closed (T A B : Finset ℕ) (at' : A ⊆ T) (bt : B ⊆ T)
    (ca : ClosedWithin n C A T) (cb : ClosedWithin n C B T) :
    let E := T \ (A ∪ B)
    occurrences n C T = occurrences n C A ∪ occurrences n C B ∪
      (occurrences n C E \ incomingCuts n C E (A∪B)) := by
  classical
  intro E
  ext p
  constructor
  · intro hp
    obtain ⟨pin,no⟩ := Finset.mem_sdiff.mp hp
    have owner := (Finset.mem_product.mp pin).1
    have smaller {J : Finset ℕ} (sub : J ⊆ T) (h : p.1 ∈ J) : p ∈ occurrences n C J := by
      have pj : p ∈ pins J := Finset.mem_product.mpr ⟨h,Finset.mem_univ _⟩
      refine Finset.mem_sdiff.mpr ⟨pj,?_⟩
      intro internalPin
      obtain ⟨j,hj,w⟩ := (Finset.mem_filter.mp internalPin).2
      exact no (Finset.mem_filter.mpr ⟨pin,j,sub hj,w⟩)
    by_cases ha : p.1 ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (smaller at' ha))
    by_cases hb : p.1 ∈ B
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (smaller bt hb))
    have pe : p.1 ∈ E := Finset.mem_sdiff.mpr ⟨owner,by simp [ha,hb]⟩
    apply Finset.mem_union_right _
    refine Finset.mem_sdiff.mpr ⟨smaller Finset.sdiff_subset pe,?_⟩
    intro cut
    obtain ⟨j,hj,wire⟩ := (Finset.mem_filter.mp cut).2
    exact no (Finset.mem_filter.mpr ⟨pin,j,(Finset.union_subset at' bt) hj,wire⟩)
  · intro h
    rcases Finset.mem_union.mp h with e | e
    · rcases Finset.mem_union.mp e with xa | xb
      · exact boundary_inclusion at' ca xa
      · exact boundary_inclusion bt cb xb
    · obtain ⟨boundary,uncut⟩ := Finset.mem_sdiff.mp e
      obtain ⟨pin,no⟩ := Finset.mem_sdiff.mp boundary
      have pt : p ∈ pins T := Finset.mem_product.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_product.mp pin).1).1,Finset.mem_univ _⟩
      refine Finset.mem_sdiff.mpr ⟨pt,?_⟩
      intro internalPin
      obtain ⟨j,hj,wire⟩ := (Finset.mem_filter.mp internalPin).2
      by_cases ab : j ∈ A∪B
      · exact uncut (Finset.mem_filter.mpr ⟨boundary,j,ab,wire⟩)
      · exact no (Finset.mem_filter.mpr ⟨pin,j,Finset.mem_sdiff.mpr ⟨hj,ab⟩,wire⟩)

theorem closed_union {A B T : Finset ℕ} (ha : ClosedWithin n C A T)
    (hb : ClosedWithin n C B T) : ClosedWithin n C (A∪B) T := by
  intro j h b i it eq
  rcases Finset.mem_union.mp h with h|h
  · exact Finset.mem_union_left _ (ha j h b i it eq)
  · exact Finset.mem_union_right _ (hb j h b i it eq)

theorem used_after_removal (ao : IsAO2 n C) {t : ℕ} {J : Finset ℕ}
    (closed : ClosedWithin n C J (andRegion n C t)) :
    let E := andRegion n C t \ J
    ∀ j ∈ E.erase t, ∃ p ∈ pins E, opnd C p.1 p.2=n+j := by
  intro E j hj
  obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hj
  obtain ⟨jt,out⟩ := Finset.mem_sdiff.mp mem
  obtain ⟨p,hp,wire⟩ := region_used ao t j (Finset.mem_erase.mpr ⟨ne,jt⟩)
  have own := (Finset.mem_product.mp hp).1
  have outside : p.1 ∉ J := fun h => out (closed _ h _ _ jt wire)
  exact ⟨p,Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨own,outside⟩,Finset.mem_univ _⟩,wire⟩

theorem cut_from_group (ao : IsAO2 n C) {t : ℕ} {A B : Finset ℕ}
    (non : A.Nonempty) (sub : A ⊆ andRegion n C t) (fresh : t ∉ A)
    (dis : Disjoint A B) (closedB : ClosedWithin n C B (andRegion n C t)) :
    let E := andRegion n C t \ (A∪B)
    ∃ p ∈ incomingCuts n C E (A∪B), ∃ i ∈ A, opnd C p.1 p.2=n+i := by
  classical
  intro E
  let i := A.max' non
  have ia : i∈A := Finset.max'_mem _ _
  have it := sub ia
  have ne : i≠t := fun eq => fresh (eq ▸ ia)
  obtain ⟨p,hp,wire⟩ := region_used ao t i (Finset.mem_erase.mpr ⟨ne,it⟩)
  have own := (Finset.mem_product.mp hp).1
  have lt := ao.2.1 p.1 (in_region.mp own).1 _ (opnd_mem_for_region ao (in_region.mp own).1 p.2)
  have outside : p.1 ∉ A∪B := by
    intro h
    rcases Finset.mem_union.mp h with h|h
    · have le : p.1 ≤ i := Finset.le_max' A p.1 h
      omega
    · exact Finset.disjoint_left.mp dis ia (closedB _ h _ _ it wire)
  have pin : p∈pins E := Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨own,outside⟩,Finset.mem_univ _⟩
  have occ : p∈occurrences n C E := by
    refine Finset.mem_sdiff.mpr ⟨pin,?_⟩
    intro h
    obtain ⟨j,je,wj⟩ := (Finset.mem_filter.mp h).2
    have eq : i=j := by omega
    exact (Finset.mem_sdiff.mp je).2 (Finset.mem_union_left _ (eq ▸ ia))
  exact ⟨p,Finset.mem_filter.mpr ⟨occ,i,Finset.mem_union_left _ ia,wire⟩,i,ia,wire⟩

theorem two_group_cuts (ao : IsAO2 n C) {t : ℕ} {A B : Finset ℕ}
    (na : A.Nonempty) (nb : B.Nonempty) (at' : A ⊆ andRegion n C t) (bt : B ⊆ andRegion n C t)
    (ta : t∉A) (tb : t∉B) (dis : Disjoint A B)
    (ac : ClosedWithin n C A (andRegion n C t)) (bc : ClosedWithin n C B (andRegion n C t)) :
    let E := andRegion n C t \ (A∪B)
    2 ≤ (incomingCuts n C E (A∪B)).card := by
  classical
  intro E
  obtain ⟨p,hp,i,ia,pi⟩ := cut_from_group ao na at' ta dis bc
  obtain ⟨q,hq,j,jb,qj⟩ := cut_from_group ao nb bt tb dis.symm ac
  rw [Finset.union_comm B A] at hq
  have ne : p≠q := by
    rintro rfl
    have eq : i=j := by omega
    exact Finset.disjoint_left.mp dis ia (eq ▸ jb)
  exact Finset.one_lt_card.mpr ⟨p,hp,q,hq,ne⟩

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4186_aux Q0.Factor S4183.S98
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem close_intersection_regions {m a b H t : ℕ} (D : Allocation G C) (mix : DoubleDirty G C m)
    (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (present : D.pivot ∈ D.components)
    (paid : ∀ i ∈ D.components.erase D.pivot, D.Local i)
    (da : a ∈ junk G C) (db : b ∈ junk G C) (pm : (gateAt C m).inputs=[n+a,n+b])
    (hH : H ∈ tops G C) (hT : t ∈ tops G C) (diff : t ≠ H)
    (affected : Influence n C m (n+H)) (external : ¬ Influence n C m (n+t))
    (labelA : t ∈ externalLabels G C H a) (labelB : t ∈ externalLabels G C H b)
    (arms : Disjoint (andRegion n C a) (andRegion n C b))
    (guardA : Disjoint (andRegion n C H) (andRegion n C a))
    (guardB : Disjoint (andRegion n C H) (andRegion n C b))
    (guardE : Disjoint ((andRegion n C H).erase H) ((andRegion n C t).erase t))
    (inside : andRegion n C a ∪ andRegion n C b ∪ (andRegion n C H).erase H ∪
      ((andRegion n C t \ ((andRegion n C a ∩ andRegion n C t) ∪ (andRegion n C b ∩ andRegion n C t))).erase t) ⊆ D.dirty D.pivot)
    (inH : H ∈ D.roots D.pivot) (inT : t ∈ D.roots D.pivot)
    (center outer : Finset (Sym2 (Fin n))) (dis : Disjoint center outer)
    (parts : D.edges D.pivot = center ∪ outer) (res : D.edges D.pivot ⊆ Ustar G C)
    (ownsH : center ⊆ gammaE G C H) (ownsT : outer ⊆ gammaE G C t) : Positive G C := by
  classical
  let A := andRegion n C a
  let B := andRegion n C b
  let Guards := andRegion n C H
  let ET := andRegion n C t
  let TA := A ∩ ET
  let TB := B ∩ ET
  let E := ET \ (TA∪TB)
  let cuts := incomingCuts n C E (TA∪TB)
  have ao := least.1
  have ainfo := (S4183.junk_iff G C a).mp da
  have binfo := (S4183.junk_iff G C b).mp db
  have tinfo := hT
  have hinfo := hH
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at tinfo hinfo
  have ra : a ∈ A := root_mem_region ainfo.1 ainfo.2.1
  have rb : b ∈ B := root_mem_region binfo.1 binfo.2.1
  have rh : H ∈ Guards := root_mem_region hinfo.1 hinfo.2.1
  have ta : t ∉ TA := fun h => ((S4183.junk_iff G C t).mp
    (dirty_region_sub ao form da (Finset.mem_inter.mp h).1)).2.2 tinfo.2.2
  have tb : t ∉ TB := fun h => ((S4183.junk_iff G C t).mp
    (dirty_region_sub ao form db (Finset.mem_inter.mp h).1)).2.2 tinfo.2.2
  have rt : t ∈ E := Finset.mem_sdiff.mpr
    ⟨root_mem_region tinfo.1 tinfo.2.1,by simpa [ta,tb]⟩
  have ka : TA ⊆ A := Finset.inter_subset_left
  have mb : TB ⊆ B := Finset.inter_subset_left
  have kt : TA ⊆ ET := Finset.inter_subset_right
  have mt : TB ⊆ ET := Finset.inter_subset_right
  have na : TA.Nonempty := intersection_nonempty labelA
  have nb : TB.Nonempty := intersection_nonempty labelB
  have clA := intersection_closed ao a t
  have clB := intersection_closed ao b t
  have deA : Disjoint E A := by
    apply Finset.disjoint_left.mpr
    intro j je ja
    obtain ⟨jt,out⟩ := Finset.mem_sdiff.mp je
    exact out (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ja,jt⟩))
  have deB : Disjoint E B := by
    apply Finset.disjoint_left.mpr
    intro j je jb
    obtain ⟨jt,out⟩ := Finset.mem_sdiff.mp je
    exact out (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨jb,jt⟩))
  have esc : E.erase t ⊆ ET.erase t := fun i hi => by
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hi
    exact Finset.mem_erase.mpr ⟨ne,(Finset.mem_sdiff.mp mem).1⟩
  have fo : Disjoint (A ∪ B) (Guards.erase H) := Finset.disjoint_union_left.mpr
    ⟨guardA.symm.mono_right (Finset.erase_subset _ _),guardB.symm.mono_right (Finset.erase_subset _ _)⟩
  have eo : Disjoint (A∪B∪Guards.erase H) (E.erase t) := Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_left.mpr ⟨deA.symm.mono_right (Finset.erase_subset _ _),
       deB.symm.mono_right (Finset.erase_subset _ _)⟩,guardE.mono_right esc⟩
  have ds := arms.mono ka mb
  have two : 2 ≤ cuts.card := two_group_cuts ao na nb kt mt ta tb ds clA.2 clB.2
  have cb : cuts ⊆ occurrences n C E := Finset.filter_subset _ _
  obtain ⟨pin,hpin,p,q,sp,sq,split⟩ := central_signals mix edge four least form hH affected da db pm
  have eUsed : ∀ j ∈ E.erase t, ∃ p ∈ pins E, opnd C p.1 p.2=n+j :=
    used_after_removal ao (closed_union clA.2 clB.2)
  have price := physical_mixer_price n C {t} A B Guards (D.dirty D.pivot) (D.roots D.pivot)
    (fun _ => E) a b H id pin (fun _ => cuts) ra rb rh (by simpa using rt)
    (region_used ao a) (region_used ao b) (region_used ao H)
    (by intro i hi; have e : i = t := Finset.mem_singleton.mp hi; subst i; exact eUsed) hpin (by simpa using cb)
    (by simp) arms fo (by simpa using eo) (by simpa using inside) inH
    (by simpa using diff) (by simpa using inT) (fun _ _ _ _ eq => eq)
  simp only [Finset.sum_singleton] at price
  have cap : (occurrences n C A).card + (occurrences n C B).card +
      ((occurrences n C Guards).erase pin).card + (occurrences n C E \ cuts).card + 2 ≤
      D.allowance D.pivot+1 := by
    unfold Allocation.allowance
    omega
  have back (i j : ℕ) (hj : j ∈ andRegion n C i) (k) : opnd C j k < n+j :=
    ao.2.1 j (in_region.mp hj).1 _ (opnd_mem_for_region ao (in_region.mp hj).1 k)
  apply finish_grouped D four edge least form (by simp [mix.exception]) present paid
    A B Guards E TA TB na nb ka mb (boundary_inclusion ka clA.1) (boundary_inclusion mb clB.1) ⟨H,rh⟩ pin hpin cuts arms guardA guardB deA deB (back a) (back b)
    (back H) center outer dis parts res ownsH p q (gateVal n C t) split
    (fun e he => (Finset.mem_filter.mp (ownsT he)).2) sp sq _ cap
  have ext := external_signal mix four least form hT external
  have part := partition_closed ET TA TB kt mt clA.2 clB.2
  change leaves n C t = occurrences n C TA ∪ occurrences n C TB ∪ (occurrences n C E \ cuts) at part
  rw [part] at ext
  exact ext

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
