import Q0Transversal

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open Q0Transversal
open scoped BigOperators

theorem rich_pow (r : ℕ) (hr : 3 ≤ r) : 2*r+2 ≤ 2^r := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hr
  induction k with
  | zero => decide
  | succ k ih =>
    change 2*((3+k)+1)+2 ≤ 2^((3+k)+1)
    rw [pow_succ]
    omega

private theorem external_strict {k p h : ℕ} (hk : 2 ≤ k) (hp : 1 ≤ p)
    (pow : 2^h ≤ k+p) (equal : k+p ≤ 2*h) : h = 2 ∧ k+p = 4 := by
  by_cases hr : 3 ≤ h
  · have := rich_pow h hr
    omega
  · interval_cases h <;> norm_num at * <;> omega

/-- Endpoint charge for any number of external one-arm leaks, with small
central batch. The only geometric exception needed is the four-slot
external double. -/
theorem low_star_charge {I : Type*} [Fintype I] (k p h : I → ℕ)
    (r s x b w : ℕ) (leaks : 2 ≤ Fintype.card I) (small : r ≤ Fintype.card I)
    (hk : ∀ i, 2 ≤ k i) (hp : ∀ i, 1 ≤ p i) (external : ∀ i, 2^(h i) ≤ k i+p i)
    (tight : ∀ i, h i = 2 → k i+p i = 4 → r ≤ 1)
    (other : 2*s ≤ b+w) :
    2*r + 2*s + ∑ i, 2*h i ≤ x+b+w+∑ i, (k i+p i+1) := by
  classical
  by_cases one : r ≤ 1
  · have hl : ∀ i, 2*h i+1 ≤ k i+p i+1 := fun i => by
      have := (twice_le_pow (h i)).trans (external i); omega
    have sum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hl i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Nat.nsmul_eq_mul, Nat.mul_one] at sum
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul,Nat.mul_one]
    omega
  · have hl : ∀ i, 2*h i+2 ≤ k i+p i+1 := by
      intro i
      by_contra! fail
      obtain ⟨he,slots⟩ := external_strict (hk i) (hp i) (external i) (by omega)
      exact one (tight i he slots)
    have sum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hl i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Nat.nsmul_eq_mul, Nat.mul_one] at sum ⊢
    omega

/-- In the deficient mixed-double case its shared block alone has at least
2^r slots. Every other external batch is charged to its own full leaf tree. -/
theorem rich_deficient_charge {I : Type*} [Fintype I] (k p h : I → ℕ)
    (r s x b w : ℕ) (rich : 3 ≤ r) (special : I)
    (he : h special = 2) (hp : p special = 2) (deficit : 2^r ≤ k special)
    (external : ∀ i, 2*h i ≤ k i+p i) (other : 2*s ≤ b+w) :
    2*r + 2*s + ∑ i, 2*h i ≤ x+b+w+∑ i, (k i+p i+1) := by
  classical
  let T := (Finset.univ : Finset I).erase special
  have rest : (∑ i ∈ T, 2*h i) ≤ ∑ i ∈ T, (k i+p i+1) :=
    Finset.sum_le_sum fun i _ => by have := external i; omega
  have split₁ := Finset.sum_erase_add (s := (Finset.univ : Finset I))
    (f := fun i => 2*h i) (Finset.mem_univ special)
  have split₂ := Finset.sum_erase_add (s := (Finset.univ : Finset I))
    (f := fun i => k i+p i+1) (Finset.mem_univ special)
  change (∑ i ∈ T, 2*h i) + 2*h special = _ at split₁
  change (∑ i ∈ T, (k i+p i+1)) + (k special+p special+1) = _ at split₂
  have := rich_pow r rich
  omega

/-- Internal batches share orientation constraints with A. External batches
outside the pool are paid from their additional slots. -/
theorem rich_pool_small_opposite {I : Type*} [Fintype I] (h p : I → ℕ)
    (internal : Finset I) (r s a b w : ℕ) (rich : 3 ≤ r) (small : s ≤ 2) (hb : 2 ≤ b)
    (pool : 2^r + ∑ i ∈ internal, 2^(h i) ≤ a+w+∑ i ∈ internal, p i)
    (paid : ∀ i ∉ internal, 2*h i ≤ p i+1) :
    2*r+2*s+∑ i, 2*h i ≤ a+b+w+∑ i, (p i+1) := by
  classical
  have inside : (∑ i ∈ internal, 2*h i) ≤ ∑ i ∈ internal, 2^(h i) :=
    Finset.sum_le_sum (fun i _ => twice_le_pow (h i))
  have outside : (∑ i ∈ internalᶜ, 2*h i) ≤ ∑ i ∈ internalᶜ, (p i+1) :=
    Finset.sum_le_sum fun i hi => paid i (Finset.mem_compl.mp hi)
  have add : (∑ i ∈ internal, p i) ≤ ∑ i ∈ internal, (p i+1) :=
    Finset.sum_le_sum fun _ _ => by omega
  have eq₁ := Finset.sum_add_sum_compl internal (fun i => 2*h i)
  have eq₂ := Finset.sum_add_sum_compl internal (fun i => p i+1)
  have := rich_pow r rich
  omega

theorem rich_pool_large_opposite {I : Type*} [Fintype I] (h p : I → ℕ)
    (internal : Finset I) (r s a b w : ℕ)
    (pool : 2^r+2^s + ∑ i ∈ internal, 2^(h i) ≤ a+b+w+∑ i ∈ internal, p i)
    (paid : ∀ i ∉ internal, 2*h i ≤ p i+1) :
    2*r+2*s+∑ i, 2*h i ≤ a+b+w+∑ i, (p i+1) := by
  classical
  have inside : (∑ i ∈ internal, 2*h i) ≤ ∑ i ∈ internal, 2^(h i) :=
    Finset.sum_le_sum (fun i _ => twice_le_pow (h i))
  have outside : (∑ i ∈ internalᶜ, 2*h i) ≤ ∑ i ∈ internalᶜ, (p i+1) :=
    Finset.sum_le_sum fun i hi => paid i (Finset.mem_compl.mp hi)
  have add : (∑ i ∈ internal, p i) ≤ ∑ i ∈ internal, (p i+1) :=
    Finset.sum_le_sum fun _ _ => by omega
  have eq₁ := Finset.sum_add_sum_compl internal (fun i => 2*h i)
  have eq₂ := Finset.sum_add_sum_compl internal (fun i => p i+1)
  have := twice_le_pow r
  have := twice_le_pow s
  omega
end PEqualNP.Outside.L_meta_4186_aux.Q1Double
