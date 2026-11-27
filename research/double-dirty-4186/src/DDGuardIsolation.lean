import DDGuardFactor

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor
attribute [local instance] gateOpDecEq

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

theorem guard_reader_in_region {m H i j : ℕ} (D : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) (ht : H ∈ tops G C)
    (affected : Influence n C m (n+H)) (hi : i ∈ (andRegion n C H).erase H)
    (rd : j ∈ readers n C i) : j ∈ andRegion n C H := by
  obtain ⟨ne,reg⟩ := Finset.mem_erase.mp hi
  rcases first_and_reader (in_region.mp reg).2.2 with eq | ⟨u,hu,au,pin,tail⟩
  · exact (ne (by omega)).elim
  · have other : u ∈ readers n C i := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu,pin⟩
    have ju := Finset.card_le_one.mp (guard_single_reader D edge least form ht affected hi) j rd u other
    subst j
    exact in_region.mpr ⟨hu,au,tail⟩

theorem guard_forward {m H g w : ℕ} (D : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) (ht : H ∈ tops G C)
    (affected : Influence n C m (n+H)) (hg : g ∈ andRegion n C H) (path : AndPath n C g w) :
    ∃ i, w=n+i ∧ i ∈ andRegion n C H := by
  induction path with
  | source => exact ⟨g,rfl,hg⟩
  | @step w j prev hj ja pin ih =>
    obtain ⟨i,rfl,reg⟩ := ih
    by_cases eq : i=H
    · subst i
      obtain ⟨bound,ha,hb⟩ := Finset.mem_filter.mp ht
      have lt := least.1.2.1 j hj _ pin
      exact (form H (Finset.mem_range.mp bound) j hj ha hb ja
        ((S4183.S90.inCone_iff n C H j).mpr ⟨hj,H,by omega,pin,Or.inl rfl⟩)).elim
    · exact ⟨j,rfl,guard_reader_in_region D edge least form ht affected
        (Finset.mem_erase.mpr ⟨eq,reg⟩) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,pin⟩)⟩

theorem guard_arm_disjoint {m H a b : ℕ} (D : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) (ht : H ∈ tops G C)
    (affected : Influence n C m (n+H)) (pins : (gateAt C m).inputs = [n+a,n+b]) :
    Disjoint (andRegion n C a ∪ andRegion n C b) ((andRegion n C H).erase H) := by
  have hcut (t : ℕ) (pin : n+t ∈ (gateAt C m).inputs) :
      Disjoint (andRegion n C t) ((andRegion n C H).erase H) := by
    apply Finset.disjoint_left.mpr
    intro g ga gg
    obtain ⟨i,eq,reg⟩ := guard_forward D edge least form ht affected (Finset.mem_of_mem_erase gg)
      (in_region.mp ga).2.2
    have it : i=t := by omega
    subst i
    have neq : t ≠ H := by
      intro e
      subst t
      have lt := least.1.2.1 m (mixer_info D).1 _ pin
      have lo {w : ℕ} (p : Influence n C m w) : n+m ≤ w := by
        induction p with
        | source => omega
        | step _ hj used ih => exact ih.trans (Nat.le_of_lt (least.1.2.1 _ hj _ used))
      have := lo affected
      omega
    have mr : m ∈ readers n C t := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (mixer_info D).1,pin⟩
    have mreg := guard_reader_in_region D edge least form ht affected (Finset.mem_erase.mpr ⟨neq,reg⟩) mr
    exact GateOp.noConfusion ((in_region.mp mreg).2.1.symm.trans (mixer_info D).2.1)
  exact Finset.disjoint_union_left.mpr ⟨hcut a (by simp [pins]),hcut b (by simp [pins])⟩

theorem guard_external_disjoint {m H t : ℕ} (D : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) (ht : H ∈ tops G C)
    (affected : Influence n C m (n+H)) (ext : t ∈ tops G C) (ne : t ≠ H) :
    Disjoint ((andRegion n C H).erase H) (andRegion n C t) := by
  apply Finset.disjoint_left.mpr
  intro g gg gt
  obtain ⟨i,eq,mem⟩ := guard_forward D edge least form ht affected
    (Finset.mem_of_mem_erase gg) (in_region.mp gt).2.2
  have it : i=t := by omega
  subst i
  have tbad := region_except_root_dirty least.1 form (Finset.mem_range.mp (Finset.mem_filter.mp ht).1)
    (Finset.mem_filter.mp ht).2.1 (Finset.mem_erase.mpr ⟨ne,mem⟩)
  exact ((S4183.junk_iff G C t).mp tbad).2.2 (Finset.mem_filter.mp ext).2.2

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
