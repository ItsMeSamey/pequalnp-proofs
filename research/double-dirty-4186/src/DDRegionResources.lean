import DDRegionClauses
import DDSharedArms

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

theorem and_path_cone (ao : IsAO2 n C) {g w : ℕ} (p : AndPath n C g w) :
    ∃ j, w=n+j ∧ (g=j ∨ InCone n C g j) := by
  induction p with
  | source => exact ⟨g,rfl,Or.inl rfl⟩
  | @step w j prev hj op pin ih =>
    obtain ⟨i,eq,chain⟩ := ih
    have lt := ao.2.1 j hj w pin
    exact ⟨j,rfl,Or.inr ((S4183.S90.inCone_iff n C g j).mpr
      ⟨hj,i,by omega,eq ▸ pin,chain⟩)⟩

theorem region_except_root_dirty {r : ℕ} (ao : IsAO2 n C) (form : PEqualNP.TopForm.TopForm G C)
    (hr : r < C.gates.length) (hand : (gateAt C r).op=.and) :
    (andRegion n C r).erase r ⊆ junk G C := by
  intro j hj
  obtain ⟨ne,reg⟩ := Finset.mem_erase.mp hj
  obtain ⟨jb,ja,path⟩ := in_region.mp reg
  obtain ⟨k,eq,e | cone⟩ := and_path_cone ao path
  · exact (ne (by omega)).elim
  · have kr : k=r := by omega
    subst k
    exact (S4183.junk_iff G C j).mpr ⟨jb,ja,fun h => form j jb r hr ja h hand cone⟩

theorem dirty_region_sub {r : ℕ} (ao : IsAO2 n C) (form : PEqualNP.TopForm.TopForm G C)
    (dirty : r ∈ junk G C) : andRegion n C r ⊆ junk G C := by
  obtain ⟨hr,hand,_⟩ := (S4183.junk_iff G C r).mp dirty
  intro j hj
  by_cases eq : j=r
  · simpa only [eq] using dirty
  · exact region_except_root_dirty ao form hr hand (Finset.mem_erase.mpr ⟨eq,hj⟩)

theorem arm_regions_disjoint {m a b : ℕ} (D : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (pa : opnd C m 0 = n+a) (pb : opnd C m 1 = n+b) : Disjoint (andRegion n C a) (andRegion n C b) := by
  obtain ⟨a',ha',ea⟩ := D.pins 0
  have e : a'=a := by omega
  subst a'
  apply Finset.disjoint_left.mpr
  intro j ja jb
  apply no_shared_arm_ancestor G C m D edge least form j (dirty_region_sub least.1 form ha' ja)
  intro w hw
  rcases Q0.reader_pin least.1 (mixer_info D).1 hw with h | h
  · rw [← h,pa]
    exact (in_region.mp ja).2.2
  · rw [← h,pb]
    exact (in_region.mp jb).2.2

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
