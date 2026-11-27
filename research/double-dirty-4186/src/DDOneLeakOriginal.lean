import DDOneLeakFinishGroup
import DDOneLeakCut
import Q1DoubleCoalesced

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4186_aux PEqualNP.EdgeOwnership Q0.Factor Triangle Allocation
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

private theorem top_facts {t : ℕ} (h : t ∈ tops G C) :
    t < C.gates.length ∧ (gateAt C t).op = .and ∧ BelowF G C t := by
  simpa only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] using h

theorem external_slot_pos {m a t : ℕ} (d : DoubleDirty G C m) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (ja : a∈junk G C) (top : t∈tops G C)
    (arm : n+a ∈ (gateAt C m).inputs) (away : ¬Influence n C m (n+t)) :
    1 ≤ (leaves n C t \ (leaves n C a ∩ leaves n C t)).card := by
  classical
  obtain ⟨ab,op,dirty⟩ := (S4183.junk_iff G C a).mp ja
  obtain ⟨tb,topAnd,clean⟩ := top_facts top
  have armSem := region_clause_semantics d least.1 form ab op (arm_boundary_plain d least.1 arm)
  have extSem := region_clause_semantics d least.1 form tb topAnd (external_plain least.1 away)
  by_contra! small
  have empty := Finset.card_eq_zero.mp (show (leaves n C t \ (leaves n C a ∩ leaves n C t)).card=0 by omega)
  have incl : leaves n C t ⊆ leaves n C a := fun p hp => (Finset.mem_inter.mp
    ((Finset.sdiff_eq_empty_iff_subset.mp empty) hp)).1
  apply dirty
  intro x ha
  exact clean x ((extSem x).mpr (fun p hp => (armSem x).mp ha p (incl hp)))

theorem singleOriented (s : OriginalCut G C) (t a b : ℕ)
    (perm : (a=s.left ∧ b=s.right) ∨ (a=s.right ∧ b=s.left))
    (left : externalLabels G C s.top a={t}) (right : externalLabels G C s.top b=∅) :
    Positive G C := by
  classical
  obtain ⟨D⟩ := s.group_data
  have pairGroup : s.group={s.top,t} := by
    rcases perm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [group,L,R,left,right]
  have tm : t∈externalLabels G C s.top a := by simp [left]
  obtain ⟨ht,yOverlap⟩ := Finset.mem_filter.mp tm
  obtain ⟨ne,tC⟩ := Finset.mem_erase.mp ht
  have htT := (Finset.mem_filter.mp tC).1
  have hT := (Finset.mem_filter.mp s.centrelessTop).1
  have actual : ∀ i, i=a ∨ i=b → i∈junk G C ∧ n+i∈(gateAt C s.mixer).inputs := by
    intro i orient
    rcases orient with rfl|rfl <;> rcases perm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [s.pins,s.leftDirty,s.rightDirty]
  obtain ⟨ja,pa⟩ := actual a (Or.inl rfl)
  obtain ⟨jb,pb⟩ := actual b (Or.inr rfl)
  obtain ⟨aa,oa,_⟩ := (S4183.junk_iff G C a).mp ja
  obtain ⟨bb,ob,_⟩ := (S4183.junk_iff G C b).mp jb
  obtain ⟨ty,oy,cleanY⟩ := top_facts htT
  obtain ⟨th,oh,cleanH⟩ := top_facts hT
  have away : ¬Influence n C s.mixer (n+t) := by
    obtain ⟨j,_,unique⟩ := unique_influenced_top s.double s.edge s.least s.form
    intro h
    exact ne ((unique _ ⟨htT,h⟩).trans (unique _ ⟨hT,s.influence⟩).symm)
  have groupEdges : D.alloc.edges D.alloc.pivot=D.own s.top ∪ D.own t := by
    simp [D.edges,pairGroup]
  have disOwn := D.distinct s.centrelessTop tC ne.symm
  have sigs : ∃ pin ∈ leaves n C s.top, ∃ p q,
      Triangle.Signal G C (leaves n C a ∪ (leaves n C s.top).erase pin) p ∧
      Triangle.Signal G C (leaves n C b ∪ (leaves n C s.top).erase pin) q ∧
      ∀ x, gateVal n C s.top x=(p x || q x) := by
    obtain ⟨g,hg,l,r,sl,sr,e⟩ := central_signals s.double s.edge s.four s.least s.form hT
      s.influence s.leftDirty s.rightDirty s.pins
    rcases perm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨g,hg,l,r,sl,sr,e⟩
    · exact ⟨g,hg,r,l,sr,sl,fun x => (e x).trans (Bool.or_comm _ _)⟩
  obtain ⟨pin,hpin,p,q,ps,qs,split⟩ := sigs
  obtain ⟨R,S,rs,un,_,ra,sa⟩ := partitionProjected G C _ (D.accepted s.top) p q split
  have up : R∪S ⊆ Ustar G C := by rw [un]; exact Finset.subset_union_left.trans (groupEdges ▸ D.res)
  have ysub : D.own t ⊆ Ustar G C := Finset.subset_union_right.trans (groupEdges ▸ D.res)
  have sy := external_signal s.double s.four s.least s.form htT away
  obtain ⟨P,pr⟩ := rows_of_signal s.four _ p ps R (Finset.subset_union_left.trans up) ra
  obtain ⟨Q,qr⟩ := rows_of_signal s.four _ q qs S (Finset.subset_union_right.trans up) sa
  obtain ⟨Y,yr⟩ := rows_of_signal s.four _ _ sy (D.own t) ysub
    (fun e he => (Finset.mem_filter.mp (D.accepted t he)).2)
  have tNot {i : ℕ} (ji : i∈junk G C) {x : ℕ} (tx : x∈tops G C) : x∉andRegion n C i := by
    intro reg
    exact ((S4183.junk_iff G C _).mp (dirty_region_sub s.least.1 s.form ji reg)).2.2 (top_facts tx).2.2
  have share : ((andRegion n C a) ∩ andRegion n C t).Nonempty := by
    by_contra no
    apply yOverlap
    exact Finset.disjoint_left.mpr fun g ga gt => no ⟨g,Finset.mem_inter.mpr ⟨ga,Finset.mem_of_mem_erase gt⟩⟩
  have be : Disjoint (andRegion n C b) (andRegion n C t) := by
    apply Finset.disjoint_left.mpr
    intro g gb gt
    have neq : g≠t := fun eq => tNot jb htT (eq ▸ gb)
    have mem : t ∈ externalLabels G C s.top b := Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨ne,tC⟩,fun aside => Finset.disjoint_left.mp aside gb (Finset.mem_erase.mpr ⟨neq,gt⟩)⟩
    simpa [right] using mem
  have stdAB := arm_regions_disjoint s.double s.edge s.least s.form
    (by simp [opnd,s.pins] : opnd C s.mixer 0=n+s.left)
    (by simp [opnd,s.pins] : opnd C s.mixer 1=n+s.right)
  have ab : Disjoint (andRegion n C a) (andRegion n C b) := by
    rcases perm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact stdAB
    · exact stdAB.symm
  have arms : andRegion n C a ∪ andRegion n C b=s.armPool := by
    rcases perm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rfl
    · exact Finset.union_comm _ _
  have ga := guard_arm_disjoint s.double s.edge s.least s.form hT s.influence s.pins
  have ga' : Disjoint (andRegion n C a ∪ andRegion n C b) ((andRegion n C s.top).erase s.top) := by
    rw [arms]; exact ga
  have ge := guard_external_disjoint s.double s.edge s.least s.form hT s.influence htT ne
  have full (i) (ji : i∈junk G C) (inPool : andRegion n C i ⊆ andRegion n C a ∪ andRegion n C b) :
      Disjoint (andRegion n C i) (andRegion n C s.top) := by
    apply Finset.disjoint_left.mpr
    intro g gi gh
    have neq : g≠s.top := fun eq => tNot ji hT (eq ▸ gi)
    exact Finset.disjoint_left.mp ga' (inPool gi) (Finset.mem_erase.mpr ⟨neq,gh⟩)
  have bound (j) (hj : j∈andRegion n C j) : 2≤(leaves n C j).card := by
    apply two_boundary _ ⟨j,hj⟩
    intro k hk f
    exact s.least.1.2.1 _ (in_region.mp hk).1 _ (opnd_mem s.least.1 (in_region.mp hk).1 f)
  have rh := root_mem_region (n:=n) th oh
  have ry := root_mem_region (n:=n) ty oy
  have rb := root_mem_region (n:=n) bb ob
  have rac := root_mem_region (n:=n) aa oa
  have rawPrice := OneLeak.merged_price s.least.1 rac rb rh ry pin hpin (tNot ja htT) share ab ga' be ge
  have fpool : D.alloc.dirty D.alloc.pivot =
      andRegion n C a ∪ andRegion n C b ∪ (andRegion n C s.top).erase s.top ∪ (andRegion n C t).erase t := by
    rw [D.pool,arms]
    simp [groupPool,pairGroup,interior,Finset.union_assoc]
  have rootcount : (D.alloc.roots D.alloc.pivot).card=2 := by
    rw [D.roots,pairGroup]; simp [ne.symm]
  have minus : leaves n C t \ (leaves n C a ∩ leaves n C t)=leaves n C t \ leaves n C a := by
    ext v; simp only [Finset.mem_sdiff,Finset.mem_inter]; tauto
  apply OneLeak.finishRows D.alloc s.four s.edge s.least s.form (by simp [s.double.exception])
    D.present D.paid D.res R S (D.own t) (by rwa [un]) rs
    (disOwn.mono_left (by rw [← un]; exact Finset.subset_union_left)) (leaves n C a) (leaves n C b)
    ((leaves n C s.top).erase pin) (leaves n C t) (leaves n C a ∩ leaves n C t)
    Finset.inter_subset_left Finset.inter_subset_right
    ((disjoint_occurrences (full a ja Finset.subset_union_left)).mono_right (Finset.erase_subset _ _))
    ((disjoint_occurrences (full b jb Finset.subset_union_right)).mono_right (Finset.erase_subset _ _))
    (OneLeak.two_shared s.least.1 share) (by have := bound _ rh; have := Finset.card_erase_add_one hpin; omega)
    (bound _ rb) (external_slot_pos s.double s.least s.form ja htT pa away) P Q Y pr qr yr
  simpa only [allowance,fpool,rootcount,minus] using rawPrice

theorem completeSingleExternalLeak (s : OriginalCut G C) : s.SingleEndpoint := by
  intro t h
  rcases h with ⟨l,r⟩ | ⟨r,l⟩
  · exact singleOriented s t s.left s.right (Or.inl ⟨rfl,rfl⟩) l r
  · exact singleOriented s t s.right s.left (Or.inr ⟨rfl,rfl⟩) r l

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
