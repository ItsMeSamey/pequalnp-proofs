import PhysicalCornerLower

namespace OnePerShore
open PEqualNP.Represents

/-- Retain only positive columns having a rejecting original neighbor. -/
def residualProfile {n m : ℕ} (A : Fin n → Fin m → Bool) (u : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun v => A u v = true ∧ ∃ i, A i v = false

/-- At the physical floor, any two nonuniversal rows with a common
residual neighbor have identical residual neighborhoods. This algebraic
condition says every nonisolated residual component is a biclique. -/
theorem residual_profiles_at_floor {n m : ℕ} {A : Fin n → Fin m → Bool}
    (rep : RepSizeAtMost A (charged A - 1)) (hk : 0 < charged A)
    (u w : Fin n) (hu : ∃ j, A u j = false) (hw : ∃ j, A w j = false)
    (common : ∃ v, v ∈ residualProfile A u ∧ v ∈ residualProfile A w) :
    residualProfile A u = residualProfile A w := by
  obtain ⟨v,vu,vw⟩ := common
  have vu' := (Finset.mem_filter.mp vu).2
  have vw' := (Finset.mem_filter.mp vw).2
  have incl (r q : Fin n) (neg : ∃ j, A r j = false)
      (rv : A r v = true) (qv : A q v = true) :
      residualProfile A r ⊆ residualProfile A q := by
    intro z hz
    obtain ⟨rz,cz⟩ := (Finset.mem_filter.mp hz).2
    by_cases qz : A q z = true
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,qz,cz⟩
    · have qz' : A q z = false := by simpa using qz
      have h := physical_corner_lower r q v z rv rz qv qz' neg vu'.2 rep
      omega
  exact Finset.Subset.antisymm (incl u w hu vu'.1 vw'.1) (incl w u hw vw'.1 vu'.1)

end OnePerShore
