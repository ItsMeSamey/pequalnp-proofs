import Research.CrownTightMass

namespace PEqualNP.Research.MissingCell
open scoped BigOperators

/-- If tight blocks are equal or disjoint, two complements differing by
one positive coordinate of subunit weight cannot both be unions of blocks. -/
theorem single_difference_precludes_tight_covers {I : Type*} [DecidableEq I]
    (blocks : Finset I → Prop) (w : I → ℚ)
    (unit : ∀ B, blocks B → (∑ j ∈ B, w j) = 1)
    (rigid : ∀ A B, blocks A → blocks B → A = B ∨ Disjoint A B)
    (X Y : Finset I) (i : I) (diff : X \ Y = {i}) (light : w i < 1)
    (coverX : ∀ j ∈ X, ∃ B, blocks B ∧ j ∈ B ∧ B ⊆ X)
    (coverY : ∀ j ∈ Y, ∃ B, blocks B ∧ j ∈ B ∧ B ⊆ Y) : False := by
  have mem : i ∈ X \ Y := by simp [diff]
  obtain ⟨ix,iy⟩ := Finset.mem_sdiff.mp mem
  obtain ⟨A,block,inside,ax⟩ := coverX i ix
  have small : A ⊆ {i} := by
    intro j hj
    rw [←diff]
    refine Finset.mem_sdiff.mpr ⟨ax hj,?_⟩
    intro jy
    obtain ⟨B,other,jb,by'⟩ := coverY j jy
    rcases rigid A B block other with eq|dis
    · exact iy (by' (eq ▸ inside))
    · exact Finset.disjoint_left.mp dis hj jb
  have eq : A = {i} := Finset.Subset.antisymm small (Finset.singleton_subset_iff.mpr inside)
  have mass := unit A block
  rw [eq,Finset.sum_singleton] at mass
  linarith

end PEqualNP.Research.MissingCell
