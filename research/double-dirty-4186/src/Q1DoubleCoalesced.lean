import Q1DoubleAssembly
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
noncomputable def group (s : OriginalCut G C) := insert s.top (s.L∪s.R)
noncomputable def interior (n : ℕ) (C : Circuit) (t : ℕ) := (andRegion n C t).erase t
noncomputable def armPool (s : OriginalCut G C) := andRegion n C s.left ∪ andRegion n C s.right
noncomputable def groupPool (s : OriginalCut G C) := s.armPool ∪ s.group.biUnion (interior n C)
theorem group_sub (s : OriginalCut G C) : s.group⊆centreless G C := by
  classical
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | either
  · exact s.centrelessTop
  rcases Finset.mem_union.mp either with l|r
  · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp l).1
  · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp r).1
theorem outside_arms (s : OriginalCut G C) {t : ℕ} (ht : t∈centreless G C)
    (away : t∉s.group) : Disjoint s.armPool (interior n C t) := by
  classical
  have h : t≠s.top ∧ t∉s.L ∧ t∉s.R := by simpa [group] using away
  have avoid (r) (no : t∉externalLabels G C s.top r) :
      Disjoint (andRegion n C r) (interior n C t) := by
    by_contra bad
    exact no (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨h.1,ht⟩,bad⟩)
  exact Finset.disjoint_left.mpr fun g hg he => (Finset.mem_union.mp hg).elim
    (fun x => Finset.disjoint_left.mp (avoid _ h.2.1) x he)
    (fun x => Finset.disjoint_left.mp (avoid _ h.2.2) x he)
theorem outside_interior (s : OriginalCut G C) {t u : ℕ} (ht : t∈centreless G C)
    (hu : u∈centreless G C) (away : t∉s.group) (ne : t≠u) :
    Disjoint (interior n C t) (interior n C u) := by
  apply exteriorDisjoint s.double s.edge s.least s.form (Finset.mem_filter.mp ht).1
    (Finset.mem_filter.mp hu).1 ne
  intro g hg _ w hw path
  obtain ⟨bound,op,_⟩ := in_region.mp (Finset.mem_of_mem_erase hg)
  apply (fun h => Finset.disjoint_left.mp (s.outside_arms ht away) h hg)
  rw [s.pins] at hw
  rcases List.mem_cons.mp hw with rfl|rest
  · exact Finset.mem_union_left _ (in_region.mpr ⟨bound,op,path⟩)
  · obtain rfl := List.mem_singleton.mp rest
    exact Finset.mem_union_right _ (in_region.mpr ⟨bound,op,path⟩)

theorem pool_outside (s : OriginalCut G C) {t : ℕ} (ht : t∈centreless G C)
    (away : t∉s.group) : Disjoint s.groupPool (interior n C t) := by
  apply Finset.disjoint_left.mpr
  intro g h he
  rcases Finset.mem_union.mp h with inside|inside
  · exact Finset.disjoint_left.mp (s.outside_arms ht away) inside he
  obtain ⟨u,hu,gu⟩ := Finset.mem_biUnion.mp inside
  exact Finset.disjoint_left.mp (s.outside_interior ht (s.group_sub hu) away (fun eq => away (eq ▸ hu))) he gu

structure GroupData (s : OriginalCut G C) where
  alloc : Allocation G C
  own : ℕ → Finset (Sym2 (Fin n))
  pivot : alloc.pivot=s.top
  present : alloc.pivot∈alloc.components
  paid : ∀ i∈alloc.components.erase alloc.pivot, alloc.Local i
  roots : alloc.roots alloc.pivot=s.group
  pool : alloc.dirty alloc.pivot=s.groupPool
  edges : alloc.edges alloc.pivot=s.group.biUnion own
  res : alloc.edges alloc.pivot⊆Ustar G C
  accepted : ∀ t, own t ⊆ gammaE G C t
  distinct : (centreless G C : Set ℕ).PairwiseDisjoint own
theorem group_data (s : OriginalCut G C) : Nonempty (GroupData s) := by
  classical
  obtain ⟨own,real,dis,all,_⟩ := originalOwnership G C s.double s.least s.form
  let ext := centreless G C \ s.group
  let I := insert s.top ext
  let F := fun t => if t=s.top then s.groupPool else interior n C t
  let T := fun t => if t=s.top then s.group else {t}
  let R := fun t => if t=s.top then s.group.biUnion own else own t
  have self : s.top∈s.group := by simp [group]
  have outsider {t : ℕ} (ht : t∈I) (ne : t≠s.top) : t∈ext := (Finset.mem_insert.mp ht).resolve_left ne
  have dirty {t : ℕ} (ht : t∈centreless G C) : interior n C t⊆junk G C := by
    obtain ⟨h,op,_⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp ht).1
    exact region_except_root_dirty s.least.1 s.form (Finset.mem_range.mp h) op
  have main : s.groupPool⊆junk G C := by
    intro g hg
    rcases Finset.mem_union.mp hg with arm|many
    · rcases Finset.mem_union.mp arm with l|r
      · exact dirty_region_sub s.least.1 s.form s.leftDirty l
      · exact dirty_region_sub s.least.1 s.form s.rightDirty r
    · obtain ⟨t,ht,mem⟩ := Finset.mem_biUnion.mp many
      exact dirty (s.group_sub ht) mem
  let A : Allocation G C := {
    components := I, pivot := s.top, dirty := F, roots := T, edges := R,
    dirtySub := by
      intro t ht
      by_cases eq : t=s.top
      · simpa [F,eq] using main
      · simpa [F,eq] using dirty (Finset.mem_sdiff.mp (outsider ht eq)).1
    rootSub := by
      intro t ht
      by_cases eq : t=s.top
      · simpa [T,eq] using s.group_sub
      · simpa [T,eq] using (Finset.mem_sdiff.mp (outsider ht eq)).1
    dirtyDisj := by
      intro i hi j hj ne
      change Disjoint (F i) (F j)
      by_cases ih : i=s.top
      · subst i
        have ex := Finset.mem_sdiff.mp (outsider hj ne.symm)
        simpa [F,ne.symm] using s.pool_outside ex.1 ex.2
      · have ex := Finset.mem_sdiff.mp (outsider hi ih)
        by_cases jh : j=s.top
        · subst j
          simpa [F,ih] using (s.pool_outside ex.1 ex.2).symm
        · have ey := Finset.mem_sdiff.mp (outsider hj jh)
          simpa [F,ih,jh] using s.outside_interior ex.1 ey.1 ex.2 ne
    rootDisj := by
      intro i hi j hj ne
      change Disjoint (T i) (T j)
      by_cases ih : i=s.top
      · subst i
        simpa [T,ne.symm] using (Finset.mem_sdiff.mp (outsider hj ne.symm)).2
      · by_cases jh : j=s.top
        · subst j
          simpa [T,ih] using (Finset.mem_sdiff.mp (outsider hi ih)).2
        · simp [T,ih,jh,ne]
    covers := by
      intro e he
      obtain ⟨t,ht,owned⟩ := Finset.mem_biUnion.mp (all.symm ▸ he)
      by_cases inG : t∈s.group
      · exact Finset.mem_biUnion.mpr ⟨s.top,Finset.mem_insert_self _ _,by
          simpa [R] using Finset.mem_biUnion.mpr ⟨t,inG,owned⟩⟩
      · have neq : t≠s.top := fun eq => inG (eq ▸ self)
        exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨ht,inG⟩),by
          simpa [R,neq] using owned⟩ }
  have here : A.pivot∈A.components := Finset.mem_insert_self _ _
  refine ⟨⟨A,own,rfl,here,?_,by simp [A,T],by simp [A,F],by simp [A,R],?_,
    fun t e h => (real t e h).2.2,dis⟩⟩
  · intro i hi
    obtain ⟨neq,mem⟩ := Finset.mem_erase.mp hi
    change i≠s.top at neq
    obtain ⟨ic,ig⟩ := Finset.mem_sdiff.mp (outsider mem neq)
    obtain ⟨t,_,uniq⟩ := unique_influenced_top s.double s.edge s.least s.form
    have ta := uniq s.top ⟨(Finset.mem_filter.mp s.centrelessTop).1,s.influence⟩
    have top := (Finset.mem_filter.mp ic).1
    have away : ¬Influence n C s.mixer (n+i) := fun h => neq ((uniq i ⟨top,h⟩).trans ta.symm)
    have pay := externalRegionCharge s.double s.four s.least s.form top away (own i)
      (fun e h => (real i e h).1) (fun e h => (real i e h).2.2)
    apply A.localOfAmple
    simpa [A,F,T,R,neq,interior] using pay
  · intro e he
    have h : e∈s.group.biUnion own := by simpa [A,R] using he
    obtain ⟨t,_,mem⟩ := Finset.mem_biUnion.mp h
    exact (real t e mem).1

theorem finishGroupAmple (s : OriginalCut G C) (B : GroupData s)
    (budget : 2*(s.group.biUnion B.own).card≤s.groupPool.card+2*s.group.card+1) :
    Positive G C := by
  apply B.alloc.finish s.four s.edge s.least s.form (by simp [s.double.exception])
  intro i hi
  by_cases eq : i=B.alloc.pivot
  · subst i
    apply B.alloc.localOfAmple
    simpa [B.edges,B.pool,B.roots] using budget
  · exact B.paid i (Finset.mem_erase.mpr ⟨eq,hi⟩)
theorem GroupData.pair {s : OriginalCut G C} (B : GroupData s) {t : ℕ}
    (pair : s.group={s.top,t}) (ne : t≠s.top) :
    Disjoint (B.own s.top) (B.own t) ∧
    B.alloc.edges B.alloc.pivot=B.own s.top ∪ B.own t ∧
    s.top∈B.alloc.roots B.alloc.pivot ∧ t∈B.alloc.roots B.alloc.pivot ∧
    s.armPool ∪ interior n C s.top ∪ interior n C t ⊆ B.alloc.dirty B.alloc.pivot := by
  classical
  have ht : t∈s.group := by simp [pair]
  refine ⟨B.distinct s.centrelessTop (s.group_sub ht) ne.symm,?_,?_,?_,?_⟩
  · simp [B.edges,pair]
  · simp [B.roots,pair]
  · simp [B.roots,pair]
  · rw [B.pool]
    simp [groupPool,pair,Finset.union_assoc]
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
