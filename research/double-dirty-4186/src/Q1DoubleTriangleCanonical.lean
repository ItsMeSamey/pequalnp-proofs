import Q1DoubleTriangleClosureGroup
import Q1DoubleCoalesced
import DDGuardIsolation

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4186_aux Q0.Factor

theorem triangleEndpoint {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (s : OriginalCut G C) : s.TriangleEndpoint := by
  classical
  intro t hl hr
  obtain ⟨B⟩ := s.group_data
  have lt : t∈s.L := by simp [hl]
  have rt : t∈s.R := by simp [hr]
  have ht := Finset.mem_erase.mp (Finset.mem_filter.mp lt).1
  have different : t≠s.top := ht.1
  have topH := (Finset.mem_filter.mp s.centrelessTop).1
  have topT := (Finset.mem_filter.mp ht.2).1
  have shape : s.group = {s.top,t} := by simp [group,hl,hr]
  have hH : s.top ∈ s.group := by simp [shape]
  have hT : t ∈ s.group := by simp [shape]
  have external : ¬ Influence n C s.mixer (n+t) := by
    intro inf
    obtain ⟨u,_,unique⟩ := unique_influenced_top s.double s.edge s.least s.form
    exact different ((unique _ ⟨topT,inf⟩).trans (unique _ ⟨topH,s.influence⟩).symm)
  have arms := arm_regions_disjoint s.double s.edge s.least s.form
    (a := s.left) (b := s.right) (by simp [opnd,s.pins]) (by simp [opnd,s.pins])
  have guard := guard_arm_disjoint s.double s.edge s.least s.form topH s.influence s.pins
  have upgrade {r : ℕ} (dirty : r∈junk G C)
      (part : Disjoint (andRegion n C r) ((andRegion n C s.top).erase s.top)) :
      Disjoint (andRegion n C s.top) (andRegion n C r) := by
    apply Finset.disjoint_left.mpr
    intro i h ireg
    by_cases eq : i=s.top
    · subst i
      exact ((S4183.junk_iff G C s.top).mp (dirty_region_sub s.least.1 s.form dirty ireg)).2.2
        (by simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at topH; exact topH.2.2)
    · exact Finset.disjoint_left.mp part ireg (Finset.mem_erase.mpr ⟨eq,h⟩)
  have ga := upgrade s.leftDirty (Finset.disjoint_union_left.mp guard).1
  have gb := upgrade s.rightDirty (Finset.disjoint_union_left.mp guard).2
  have ge := guard_external_disjoint s.double s.edge s.least s.form topH s.influence topT different
  refine Triangle.close_intersection_regions B.alloc s.double s.four s.edge s.least s.form B.present B.paid
    s.leftDirty s.rightDirty s.pins topH topT different s.influence external lt rt arms ga gb
    (ge.mono_right (Finset.erase_subset _ _)) ?_ ?_ ?_ (B.own s.top) (B.own t)
    (B.distinct s.centrelessTop ht.2 different.symm) ?_ B.res (B.accepted _) (B.accepted _)
  · rw [B.pool]
    intro i hi
    rcases Finset.mem_union.mp hi with h | e
    · rcases Finset.mem_union.mp h with arm | guardMem
      · exact Finset.mem_union_left _ arm
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_,hH,guardMem⟩)
    · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp e
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨_,hT,Finset.mem_erase.mpr ⟨ne,(Finset.mem_sdiff.mp mem).1⟩⟩)
  · rwa [B.roots]
  · rwa [B.roots]
  · simp [B.edges,shape]

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
