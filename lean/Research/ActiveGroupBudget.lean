import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Polynomial root budgets and active-group capacity for replacement layouts. -/

namespace LayoutActive

/-- An inactive measurement has the whole group in its kernel. An observed
row which factors through that measurement must vanish on the whole group. -/
theorem row_zero_of_inactive {K X Y : Type*} [Field K]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (measure : X →ₗ[K] Y) (row : X →ₗ[K] K)
    (inactive : measure = 0) (factors : LinearMap.ker measure ≤ LinearMap.ker row) (x : X) :
    row x = 0 := by
  apply LinearMap.mem_ker.mp
  apply factors
  simp [inactive]

end LayoutActive

namespace LayoutActive

theorem inactive_mismatch_cap {K ι V : Type*} [Field K]
    (T : Finset ι) (point : ι → K) (distinct : Set.InjOn point (T : Set ι))
    (p : V → Polynomial K) (R : ℕ)
    (normalized : ∀ v, (p v).eval 0 = 1) (degree_bound : ∀ v, (p v).natDegree ≤ R)
    (bad : V → ι → Prop) [∀ v, DecidablePred (bad v)]
    (vanishes : ∀ v t, t ∈ T → bad v t → (p v).eval (point t) = 0)
    (v : V) : (T.filter (bad v)).card ≤ R := by
  classical
  let S := T.filter (bad v)
  have hT (i : S) : (i : ι) ∈ T := (Finset.mem_filter.mp i.property).1
  have hi : Function.Injective (fun i : S => point i.val) :=
    fun i j h => Subtype.ext (distinct (hT i) (hT j) h)
  have hz (i : S) : (p v).eval (point i.val) = 0 :=
    vanishes v i.val (hT i) (Finset.mem_filter.mp i.property).2
  apply le_trans _ (degree_bound v)
  by_contra! h
  have hc : (p v).natDegree < Fintype.card S := by simpa [S] using h
  have heq := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (p v) hi hz hc
  simpa [heq] using normalized v

end LayoutActive

open scoped BigOperators Classical

namespace LayoutActive

theorem supportCount {τ ν γ : Type*}
    (T : Finset τ) (V : Finset ν) (G : Finset γ)
    (E : τ → ν → Prop) (active : τ → γ → Prop) (owner : τ → ν → γ)
    (R : ℕ) (s : τ → ℕ)
    (howner : ∀ t ∈ T, ∀ v ∈ V, owner t v ∈ G)
    (hinactive : ∀ v ∈ V, (T.filter (fun t => E t v ∧ ¬active t (owner t v))).card ≤ R)
    (hfiber : ∀ t ∈ T, ∀ g ∈ G, active t g →
      (V.filter (fun v => E t v ∧ owner t v = g)).card ≤ s t) :
    ∑ v ∈ V, (T.filter (fun t => E t v)).card ≤
      V.card * R + ∑ t ∈ T, s t * (G.filter (active t)).card := by
  classical
  let act := fun t v => E t v ∧ active t (owner t v)
  let idle := fun t v => E t v ∧ ¬active t (owner t v)
  have split (v : ν) : (T.filter (fun t => E t v)).card =
      (T.filter (fun t => idle t v)).card + (T.filter (fun t => act t v)).card := by
    simpa [idle, act, Finset.filter_filter, Nat.add_comm] using
      ((T.filter (fun t => E t v)).card_filter_add_card_filter_not
        (fun t => active t (owner t v))).symm
  have swap : ∑ v ∈ V, (T.filter (fun t => act t v)).card =
      ∑ t ∈ T, (V.filter (fun v => act t v)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have byRow (t : τ) (ht : t ∈ T) : (V.filter (act t)).card ≤ s t * (G.filter (active t)).card := by
    let W := V.filter (E t)
    let H := G.filter (active t)
    have equiv : V.filter (act t) = W.filter (fun v => owner t v ∈ H) := by
      ext v
      simp only [W,H,act,Finset.mem_filter]
      constructor
      · rintro ⟨hv,he,ha⟩
        exact ⟨⟨hv,he⟩,howner t ht v hv,ha⟩
      · rintro ⟨⟨hv,he⟩,_,ha⟩
        exact ⟨hv,he,ha⟩
    rw [equiv, ← Finset.sum_card_fiberwise_eq_card_filter W H (owner t)]
    calc
      _ ≤ ∑ _g ∈ H, s t := Finset.sum_le_sum (fun g hg => by
        obtain ⟨hg', ha⟩ := Finset.mem_filter.mp hg
        simpa [W, Finset.filter_filter] using hfiber t ht g hg' ha)
      _ = _ := by simp [H,Nat.mul_comm]
  simp_rw [split]
  rw [Finset.sum_add_distrib, swap]
  apply Nat.add_le_add _ (Finset.sum_le_sum byRow)
  calc
    _ ≤ ∑ _v ∈ V, R := Finset.sum_le_sum hinactive
    _ = _ := by simp

end LayoutActive

namespace LayoutActive

/-- A dense incidence set and a bounded residual force a large product
at one of the participating layouts. -/
theorem exists_large_layout {α : Type*} (T : Finset α) (s a : α → ℕ)
    (edges n R : ℕ) (γ : ℚ) (hne : T.Nonempty)
    (density : γ * n * T.card ≤ (edges : ℚ))
    (budget : (R : ℚ) ≤ γ * T.card / 2)
    (mismatch : edges ≤ n * R + ∑ t ∈ T, s t * a t) :
    ∃ t ∈ T, γ * n / 2 ≤ (s t : ℚ) * a t := by
  by_contra! hsmall
  have hsum : (∑ t ∈ T, (s t : ℚ) * a t) < ∑ _t ∈ T, γ * n / 2 :=
    Finset.sum_lt_sum_of_nonempty hne hsmall
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hm : (edges : ℚ) ≤ (n : ℚ) * R + ∑ t ∈ T, (s t : ℚ) * a t := by
    exact_mod_cast mismatch
  have hr := mul_le_mul_of_nonneg_left budget (by positivity : 0 ≤ (n : ℚ))
  linarith

end LayoutActive

open scoped BigOperators Classical

namespace LayoutActive

def measured {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] (M : X →ₗ[K] Y) : Prop := M ≠ 0

/-- Total mismatches are bounded by the per-variable polynomial root budget and
the combined capacity of groups with nonzero measurement maps. The source and
measurement spaces may vary with the point and group. -/
theorem polynomial_layout_budget {K τ ν ι : Type*} [Field K]
    (T : Finset τ) (V : Finset ν) (G : Finset ι)
    (X Y : τ → ι → Type*)
    [∀ t g, AddCommGroup (X t g)] [∀ t g, Module K (X t g)]
    [∀ t g, AddCommGroup (Y t g)] [∀ t g, Module K (Y t g)]
    (measure : ∀ t g, X t g →ₗ[K] Y t g)
    (owner : τ → ν → ι) (E : τ → ν → Prop) (s : τ → ℕ) (R : ℕ)
    (point : τ → K) (distinct : Set.InjOn point (T : Set τ))
    (p : ν → Polynomial K)
    (normalized : ∀ v ∈ V, (p v).eval 0 = 1)
    (degree_bound : ∀ v ∈ V, (p v).natDegree ≤ R)
    (row : ∀ t v, X t (owner t v) →ₗ[K] K)
    (coord : ∀ t v, X t (owner t v))
    (howner : ∀ t ∈ T, ∀ v ∈ V, owner t v ∈ G)
    (hfiber : ∀ t ∈ T, ∀ g ∈ G, (V.filter (fun v => owner t v = g)).card ≤ s t)
    (hdiag : ∀ t ∈ T, ∀ v ∈ V, E t v → (p v).eval (point t) = row t v (coord t v))
    (kernel : ∀ t ∈ T, ∀ v ∈ V, E t v →
      LinearMap.ker (measure t (owner t v)) ≤ LinearMap.ker (row t v)) :
    ∑ v ∈ V, (T.filter (fun t => E t v)).card ≤ V.card * R +
      ∑ t ∈ T, s t * (G.filter (fun g => measured (measure t g))).card := by
  classical
  refine (supportCount T V G E (fun t g => measured (measure t g)) owner R s howner ?_ ?_)
  · intro v hv
    let bad := fun (_ : Unit) t => E t v ∧ ¬measured (measure t (owner t v))
    convert inactive_mismatch_cap T point distinct (fun _ : Unit => p v) R
      (fun _ => normalized v hv) (fun _ => degree_bound v hv) bad (by
        intro _ t ht h
        obtain ⟨he, hz⟩ := h
        rw [hdiag t ht v hv he]
        exact row_zero_of_inactive _ _ (not_not.mp hz) (kernel t ht v hv he) _) () using 1
  · intro t ht g hg _
    apply le_trans _ (hfiber t ht g hg)
    apply Finset.card_le_card
    intro v hv
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2.2⟩

end LayoutActive

namespace LayoutActive

/-- Each group can attain two distinct measurements. Independent choice realizes a
different joint measurement for every Boolean vector indexed by the groups. -/
theorem two_pow_le_attainable {G : Type*} [Fintype G]
    {X : G → Type*} {M : G → Type*}
    (measure : (g : G) → X g → M g) (lo hi : (g : G) → X g)
    (separate : ∀ g, measure g (lo g) ≠ measure g (hi g))
    [Fintype (Set.range (fun x : (g : G) → X g => fun g => measure g (x g)))] :
    2 ^ Fintype.card G ≤
      Fintype.card (Set.range (fun x : (g : G) → X g => fun g => measure g (x g))) := by
  classical
  let pick (b : G → Bool) (g : G) : X g := if b g then hi g else lo g
  let encode (b : G → Bool) :
      Set.range (fun x : (g : G) → X g => fun g => measure g (x g)) :=
    ⟨fun g => measure g (pick b g), pick b, rfl⟩
  have inj : Function.Injective encode := by
    intro b c h
    funext g
    have hcoord := congrFun (congrArg Subtype.val h) g
    change measure g (pick b g) = measure g (pick c g) at hcoord
    have reverse := (separate g).symm
    cases hb : b g <;> cases hc : c g <;> simp_all [pick]
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective encode inj

end LayoutActive

namespace LayoutActive

theorem exists_nonzero_unit_column {ι K Y : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] [AddCommGroup Y] [Module K Y]
    (M : (ι → K) →ₗ[K] Y) (active : M ≠ 0) :
    ∃ i : ι, M 0 ≠ M (Pi.single i 1) := by
  by_contra! h
  apply active
  apply LinearMap.pi_ext
  intro i x
  have hz : M (Pi.single i 1) = 0 := by simpa using (h i).symm
  have hs : Pi.single i x = x • (Pi.single i (1 : K)) := by
    rw [← Pi.single_smul']; simp
  rw [hs, map_smul, hz, smul_zero, LinearMap.zero_apply]

def boolColumn {ι K : Type*} [Zero K] [One K] (b : ι → Bool) : ι → K :=
  fun i => if b i then 1 else 0

theorem two_pow_le_boolean_column_measurements {G K : Type*} [Fintype G] [Field K]
    {I Y : G → Type*} [∀ g, Fintype (I g)] [∀ g, DecidableEq (I g)]
    [∀ g, AddCommGroup (Y g)] [∀ g, Module K (Y g)]
    (M : (g : G) → (I g → K) →ₗ[K] Y g) (active : ∀ g, M g ≠ 0)
    [Fintype (Set.range (fun x : (g : G) → I g → Bool => fun g => M g (boolColumn (x g))))]
    : 2 ^ Fintype.card G ≤ Fintype.card
      (Set.range (fun x : (g : G) → I g → Bool => fun g => M g (boolColumn (x g)))) := by
  classical
  choose idx hi using fun g => exists_nonzero_unit_column (M g) (active g)
  apply two_pow_le_attainable (fun g (b : I g → Bool) => M g (boolColumn b))
    (fun _ _ => false) (fun g j => decide (j = idx g))
  intro g
  have hz : boolColumn (K := K) (fun _ : I g => false) = 0 := by ext; simp [boolColumn]
  have hu : boolColumn (K := K) (fun j : I g => decide (j = idx g)) = Pi.single (idx g) 1 := by
    ext j
    by_cases he : j = idx g
    · subst j; simp [boolColumn]
    · simp [boolColumn, he]
  rw [hz, hu]
  exact hi g

end LayoutActive

namespace LayoutActive

theorem density_le_mean_sq (γ : ℚ) (n s a : ℕ)
    (h : γ * n / 2 ≤ (s : ℚ) * a) :
    γ * n / 2 ≤ (((s : ℚ) + a) / 2) ^ 2 := by
  nlinarith [sq_nonneg ((s : ℚ) - a)]

theorem double_le_sum_of_sq_le_product (k s a : ℕ) (h : k * k ≤ s * a) :
    2 * k ≤ s + a := by
  by_contra! hlt
  have hs : (s+a)*(s+a) < (2*k)*(2*k) := Nat.mul_self_lt_mul_self hlt
  have hi : ((s : ℤ)+a)*((s : ℤ)+a) < (2*(k : ℤ))*(2*(k : ℤ)) := by exact_mod_cast hs
  have hh : (k : ℤ)*k ≤ (s : ℤ)*a := by exact_mod_cast h
  nlinarith [sq_nonneg ((s : ℤ) - a)]

theorem pow_two_double_le_of_sq_le_product (k s a : ℕ) (h : k * k ≤ s * a) :
    (2 : ℕ) ^ (2 * k) ≤ 2 ^ s * 2 ^ a := by
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by decide) (double_le_sum_of_sq_le_product k s a h)

end LayoutActive


namespace LayoutActive

/-- With at least one visit for every local assignment and attainable tuple,
a dense mismatch set forces a large visit count at some evaluation point. -/
theorem exists_large_full_scan {τ : Type*} (T : Finset τ) (s a visits : τ → ℕ)
    (edges n R k : ℕ) (γ : ℚ) (nonempty : T.Nonempty)
    (density : γ * n * T.card ≤ (edges : ℚ)) (lowDegree : (R : ℚ) ≤ γ * T.card / 2)
    (budget : edges ≤ n * R + ∑ t ∈ T, s t * a t)
    (threshold : (k : ℚ) ^ 2 ≤ γ * n / 2)
    (fullScan : ∀ t ∈ T, 2 ^ (s t) * 2 ^ (a t) ≤ visits t) :
    ∃ t ∈ T, 2 ^ (2 * k) ≤ visits t := by
  obtain ⟨t, ht, h⟩ := exists_large_layout T s a edges n R γ nonempty density lowDegree budget
  have hq : (k : ℚ) * k ≤ (s t : ℚ) * a t := by simpa [pow_two] using threshold.trans h
  have hk : k * k ≤ s t * a t := by exact_mod_cast hq
  exact ⟨t, ht, (pow_two_double_le_of_sq_le_product k (s t) (a t) hk).trans (fullScan t ht)⟩

end LayoutActive
