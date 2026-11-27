import DDRegionResources
import DDMixerRoot

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

theorem kept_path_split {m g w : ℕ} (D : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) (dirty : g∈junk G C)
    (reach : Influence n C g w) (keep : Kept G C w) :
    AndPath n C g w ∨ Influence n C m w := by
  obtain ⟨gb,ga,_⟩ := (S4183.junk_iff G C g).mp dirty
  obtain ⟨reader,out,_⟩ := main_real n G C edge least form
  induction reach with
  | source => exact Or.inl .source
  | @step j v prev hj pin ih =>
    rcases ih (kept_nonclean edge least form hj _ keep pin) with path | viaM
    · rcases least.1.1 _ (S4183.S90.gateAt_mem hj) with ja | jo
      · exact Or.inl (.step path hj ja pin)
      · have opEnd : ∃ i, v=n+i ∧ i<C.gates.length ∧ (gateAt C i).op=.and := by
          cases path with
          | source => exact ⟨g,rfl,gb,ga⟩
          | step _ b op _ => exact ⟨_,rfl,b,op⟩
        obtain ⟨i,rfl,hi,ia⟩ := opEnd
        by_cases clean : BelowF G C i
        · exfalso
          have rd : j ∈ readers n C i := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,pin⟩
          have ne : n+i ≠ C.output := by
            intro eq
            have ix : C.output-n=i := by omega
            rw [ix] at out
            simpa [out] using rd
          obtain ⟨r,only,hop,hb⟩ := reader i hi clean ne
          rw [only,Finset.mem_singleton] at rd
          subst r
          exact keep j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hop,hb⟩) rfl
        · have jm := dirty_or_eq D least.1 ((S4183.junk_iff G C i).mpr ⟨hi,ia,clean⟩) hj pin jo
          subst j
          exact Or.inr .source
    · exact Or.inr (.step viaM hj pin)

theorem guard_single_reader {m H g : ℕ} (D : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) (ht : H ∈ tops G C)
    (affected : Influence n C m (n+H)) (hg : g ∈ (andRegion n C H).erase H) :
    (readers n C g).card ≤ 1 := by
  obtain ⟨hHr,hHa,_⟩ := Finset.mem_filter.mp ht
  have junk := region_except_root_dirty least.1 form (Finset.mem_range.mp hHr) hHa hg
  obtain ⟨gl,_,bad⟩ := (S4183.junk_iff G C g).mp junk
  have toH := (in_region.mp (Finset.mem_of_mem_erase hg)).2.2
  obtain ⟨T,_,unique⟩ := unique_influenced_top D edge least form
  apply dominated_unique G C g gl bad edge least form (live_dirty G C g gl bad edge least)
  intro t top inf x yes
  have kept : Kept G C (n+t) := by
    intro i hi eq
    have it : i=t := by omega
    subst i
    exact GateOp.noConfusion ((Finset.mem_filter.mp top).2.1.symm.trans (Finset.mem_filter.mp hi).2.1)
  rcases kept_path_split D edge least form junk inf kept with apos | via
  · exact path_implies_source least.1 apos x yes
  · have eq := (unique t ⟨top,via⟩).trans (unique H ⟨ht,affected⟩).symm
    subst t
    exact path_implies_source least.1 toH x yes

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
