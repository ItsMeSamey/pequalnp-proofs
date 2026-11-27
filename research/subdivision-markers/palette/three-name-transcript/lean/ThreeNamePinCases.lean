import ThreeNamePinReduction

namespace ThreeNamePinReduction
open ExactPlaneGaussian
variable {I B : Type*} [DecidableEq I] {d : ℕ} [AddCommGroup B] [Module F B]

/-- When two projected values agree, the original-index coefficient mask
decodes their difference, and its support is contained in the pins. -/
theorem lift_coefficients [Fintype I] (col : I → V d) (pins : List I) (x y : V d)
    (eq : project col pins x = project col pins y) :
    ∃ mask, solve pins col (x-y) = some mask ∧ decode col mask = x-y ∧
      ∀ i ∉ pins, mask i = 0 := by
  apply coeffs_of_killed
  rw [map_sub,eq,sub_self]

private theorem compatible_of_success (col : I → V d) (name : (B × F) →ₗ[F] V d)
    (pins : List I) (h : ∃ A, pins.toFinset ⊆ A ∧ Exact col name A) :
    Compatible col name pins := by
  by_contra bad
  exact incompatible_no col name pins bad h

/-- Rank-deficient name branch. For a two-dimensional tag space the last
condition is exactly independence of the two projected tag-basis columns. -/
theorem deficient_iff (col : I → V d) (name : (B × F) →ₗ[F] V d) (pins : List I)
    (deficient : ¬ Function.Injective ((project col pins).comp name)) :
    (∃ A, pins.toFinset ⊆ A ∧ Exact col name A) ↔
      project col pins (name (0,1)) = 0 ∧
      Function.Injective (((project col pins).comp name).comp (LinearMap.inl F B F)) := by
  let q := project col pins
  let L := q.comp name
  constructor
  · intro h
    have compat := compatible_of_success col name pins h
    have axis : q (name (0,1)) = 0 := by
      by_contra hn
      exact deficient (named_injective _ _ _ compat hn)
    refine ⟨axis, LinearMap.ker_eq_bot.mp (le_antisymm ?_ bot_le)⟩
    intro z hz
    change q (name (z,0)) = 0 at hz
    exact (Submodule.mem_bot F).mpr (compat z 0 ((killed_iff _ _ _).mp hz))
  · rintro ⟨axis,inj⟩
    have zero_axis (y : F) : L (0,y) = 0 := by
      have h : y • ((0:B),(1:F)) = (0,y) := by ext <;> simp
      rw [← h,map_smul]
      change y • q (name (0,1)) = 0
      rw [axis,smul_zero]
    have compat : Compatible col name pins := by
      intro z y mem
      have hz : L (z,y) = 0 := (killed_iff _ _ _).mpr mem
      have split : ((z,0) : B × F) + (0,y) = (z,y) := by simp
      rw [← split,map_add,zero_axis,add_zero] at hz
      apply inj
      change L (z,0) = L (0,0)
      exact hz.trans (map_zero L).symm
    exact ⟨pins.toFinset,fun _ hi => hi,axis_yes col name pins compat axis⟩

#print axioms deficient_iff
#print axioms lift_coefficients
end ThreeNamePinReduction
