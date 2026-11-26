import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace ExactPlaneFieldSampler
open scoped BigOperators
open Classical
abbrev F := ZMod 2
abbrev V (n : ℕ) := Fin n → F
abbrev D (K : Type*) [AddCommGroup K] [Module F K] := K →ₗ[F] F

def sample {K : Type*} [Field K] [Algebra F K] (m : ℕ) (x : K) :
    D K →ₗ[F] V m where
  toFun τ j := τ (x ^ j.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def seed (K : Type*) [Field K] [Fintype K] [Algebra F K]
    [Fintype (D K)] (m : ℕ) : Finset (V m) :=
  Finset.univ.image (fun a : K × D K => sample m a.1 a.2)

theorem seed_card_le (K : Type*) [Field K] [Fintype K] [Algebra F K]
    [Fintype (D K)] (m : ℕ) :
    (seed K m).card ≤ Fintype.card K * Fintype.card (D K) := by
  classical
  simpa [seed] using (Finset.card_image_le (s:=Finset.univ)
    (f:=fun a : K × D K => sample m a.1 a.2))

private def unitVec {m : ℕ} (i : Fin m) : V m := fun j => if i=j then 1 else 0

private noncomputable def wordPoly (K : Type*) [Field K] [Algebra F K] {m : ℕ}
    (l : D (V m)) : Polynomial K :=
  Polynomial.ofFn m (fun i => algebraMap F K (l (unitVec i)))

private theorem word_ne (K : Type*) [Field K] [Algebra F K] {m : ℕ}
    (l : D (V m)) (hl : l ≠ 0) : wordPoly K l ≠ 0 := by
  classical
  intro zero
  have coord (i : Fin m) : l (unitVec i) = 0 := by
    apply (algebraMap F K).injective
    have h := congrArg (fun p : Polynomial K => p.coeff i.val) zero
    simpa [wordPoly,Polynomial.ofFn_coeff_eq_val_of_lt _ i.isLt] using h
  apply hl
  apply LinearMap.ext
  intro v
  rw [LinearMap.pi_apply_eq_sum_univ l v]
  change (∑ i : Fin m, v i • l (unitVec i)) = 0
  simp [coord]

private theorem word_eval {K : Type*} [Field K] [Algebra F K] {m : ℕ}
    (l : D (V m)) (x : K) (τ : D K) :
    l (sample m x τ) = τ ((wordPoly K l).eval x) := by
  classical
  rw [LinearMap.pi_apply_eq_sum_univ l,wordPoly,Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.eval_monomial,← Algebra.smul_def,map_smul]
  change τ (x ^ i.val) * l (unitVec i) = l (unitVec i) * τ (x ^ i.val)
  exact mul_comm _ _

theorem field_hits (m R : ℕ) (K : Type*) [Field K] [Fintype K] [Algebra F K]
    [Fintype (D K)] (hm : 0 < m) (large : m * 2^R < Fintype.card K) :
    ∀ k ≤ R, ∀ f : V m →ₗ[F] V k, Function.Surjective f →
      ∀ y, ∃ s ∈ seed K m, f s = y := by
  classical
  intro k hk f onto y
  let e := (Pi.basisFun F (Fin k)).toDualEquiv
  letI : Fintype (D (V k)) := Fintype.ofEquiv (V k) e.toEquiv
  have dualCard : Fintype.card (D (V k)) = 2^k := by
    rw [← Fintype.card_congr e.toEquiv]
    simp [V,F,ZMod.card]
  let active : Finset (D (V k)) := Finset.univ.erase 0
  let p := fun l : D (V k) => wordPoly K (l.comp f)
  let roots := fun l : D (V k) => (p l).roots.toFinset
  have cost (l : D (V k)) : (roots l).card ≤ m-1 := by
    refine ((p l).roots.toFinset_card_le.trans (Polynomial.card_roots' _)).trans ?_
    have h := Polynomial.ofFn_natDegree_lt (R:=K) hm
      (fun i : Fin m => algebraMap F K ((l.comp f) (unitVec i)))
    change (p l).natDegree < m at h
    omega
  have cap : (active.biUnion roots).card ≤ (2^k-1)*(m-1) := by
    have h := Finset.card_biUnion_le_card_mul active roots (m-1) (fun l _ => cost l)
    simpa [active,dualCard,Finset.card_erase_of_mem] using h
  have short : (active.biUnion roots).card < Fintype.card K := by
    apply lt_of_le_of_lt cap
    apply lt_of_le_of_lt _ large
    rw [mul_comm m]
    exact Nat.mul_le_mul ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by decide) hk))
      (Nat.sub_le _ _)
  obtain ⟨x,hx⟩ : ∃ x : K, x ∉ active.biUnion roots := by
    by_contra! h
    have all : active.biUnion roots = Finset.univ := Finset.eq_univ_of_forall h
    simpa [all] using short
  let g := f.comp (sample m x)
  have surj : Function.Surjective g := by
    apply (LinearMap.dualMap_injective_iff (f := g)).mp
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro l annih
    by_contra nz
    have never : x ∉ roots l := fun hit => hx (Finset.mem_biUnion.mpr
      ⟨l,Finset.mem_erase.mpr ⟨nz,Finset.mem_univ _⟩,hit⟩)
    have lcomp : l.comp f ≠ 0 := by
      intro nul
      apply nz
      apply LinearMap.ext
      intro z
      obtain ⟨v,rfl⟩ := onto z
      exact DFunLike.congr_fun nul v
    have nonzero : (p l).eval x ≠ 0 := by
      intro nul
      apply never
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (word_ne K _ lcomp)).mpr nul)
    obtain ⟨τ,hτ⟩ := Module.Projective.exists_dual_ne_zero F nonzero
    apply hτ
    rw [← word_eval (l.comp f)]
    exact DFunLike.congr_fun annih τ
  obtain ⟨τ,hτ⟩ := surj y
  exact ⟨sample m x τ,Finset.mem_image.mpr ⟨(x,τ),Finset.mem_univ _,rfl⟩,hτ⟩

theorem zero_hits (R : ℕ) : ∀ k ≤ R, ∀ f : V 0 →ₗ[F] V k, Function.Surjective f →
    ∀ y, ∃ s ∈ ({0} : Finset (V 0)), f s = y := by
  intro k _ f onto y
  obtain ⟨v,rfl⟩ := onto y
  exact ⟨0,Finset.mem_singleton_self _,congrArg f (Subsingleton.elim _ _)⟩

end ExactPlaneFieldSampler
