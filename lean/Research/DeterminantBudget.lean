import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Roots

open Polynomial
open scoped BigOperators
namespace DeterminantBudget
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Vanishing of an entire set of columns at a node forces the corresponding
power of the node's linear polynomial to divide the determinant. -/
theorem columns_dvd (B : Matrix ι ι K[X]) (t : K) (s : Finset ι)
    (h : ∀ j ∈ s, ∀ i, (B i j).eval t = 0) :
    (X - C t) ^ s.card ∣ B.det := by
  classical
  let v : ι → K[X] := fun j => if j ∈ s then X - C t else 1
  have hv (i j : ι) : v j ∣ B i j := by
    by_cases hj : j ∈ s
    · simpa [v, hj] using (dvd_iff_isRoot.mpr (h j hj i) : X - C t ∣ B i j)
    · simp [v, hj]
  choose q hq using hv
  have hB : B = Matrix.of (fun i j => v j * q i j) := by
    apply Matrix.ext
    intro i j
    exact hq i j
  have hdet : B.det = (∏ j, v j) * (Matrix.of q).det := hB ▸ Matrix.det_mul_row v (Matrix.of q)
  rw [hdet]
  have hvprod : ∏ j, v j = (X - C t) ^ s.card := by
    simp [v]
  rw [hvprod]
  exact dvd_mul_right _ _

/-- The distinct-node budget given local divisibility certificates. -/
theorem budget (p : K[X]) (hp : p ≠ 0) (nodes : Finset K) (k : K → ℕ)
    (h : ∀ t ∈ nodes, (X - C t) ^ k t ∣ p) :
    ∑ t ∈ nodes, k t ≤ p.natDegree := by
  classical
  let cover := nodes ∪ p.roots.toFinset
  calc
    ∑ t ∈ nodes, k t ≤ ∑ t ∈ nodes, p.roots.count t := by
      apply Finset.sum_le_sum
      intro t ht
      rw [count_roots]
      exact (le_rootMultiplicity_iff hp).mpr (h t ht)
    _ ≤ ∑ t ∈ cover, p.roots.count t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left)
      simp
    _ = p.roots.card := Multiset.sum_count_eq_card (fun _ ha => Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha))
    _ ≤ p.natDegree := card_roots' p

/-- The corank at a node lower-bounds the order of vanishing of the determinant. -/
theorem nullity_dvd (B : Matrix ι ι K[X]) (t : K) :
    (X - C t) ^ (Fintype.card ι - ((evalRingHom t).mapMatrix B).rank) ∣ B.det := by
  classical
  let ev := (evalRingHom t).mapMatrix (m := ι)
  let const := (C : K →+* K[X]).mapMatrix (m := ι)
  let M := ev B
  obtain ⟨V, U, e, hV, hU, he⟩ := M.exists_rank_normal_form
  let T := const V * B * const U
  let emb := (Function.Embedding.inr.trans e.symm.toEmbedding :
    Fin (Fintype.card ι - M.rank) ↪ ι)
  let s := Finset.univ.map emb
  have hconst (W : Matrix ι ι K) : ev (const W) = W := by
    apply Matrix.ext
    intro i j
    simp [ev, const, RingHom.mapMatrix_apply]
  have hT : ev T = (Matrix.fromBlocks 1 0 0 0).submatrix e e := by
    simpa only [T, map_mul, hconst] using he
  have hzero : ∀ j ∈ s, ∀ i, (T i j).eval t = 0 := by
    intro j hj i
    obtain ⟨l, _, rfl⟩ := Finset.mem_map.mp hj
    have hij := congrFun (congrFun hT i) (emb l)
    change (T i (emb l)).eval t = (Matrix.fromBlocks 1 0 0 0) (e i) (e (emb l)) at hij
    rw [hij]
    have hel : e (emb l) = Sum.inr l := e.apply_symm_apply _
    rw [hel]
    cases e i <;> rfl
  have hd := columns_dvd T t s hzero
  have hs : s.card = Fintype.card ι - M.rank := by simp [s]
  rw [hs, show T = const V * B * const U from rfl, Matrix.det_mul, Matrix.det_mul] at hd
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (hU.map const)
  have hv := (Matrix.isUnit_iff_isUnit_det _).mp (hV.map const)
  change (X - C t) ^ (Fintype.card ι - M.rank) ∣ B.det
  simpa only [hu.dvd_mul_right, hv.dvd_mul_left] using hd

/-- Sum of coranks at distinct field elements, for any regular square polynomial matrix. -/
theorem nullity_budget (B : Matrix ι ι K[X]) (hB : B.det ≠ 0) (nodes : Finset K) :
    ∑ t ∈ nodes, (Fintype.card ι - ((evalRingHom t).mapMatrix B).rank) ≤ B.det.natDegree := by
  apply budget B.det hB
  exact fun t _ => nullity_dvd B t

/-- The normalization at zero guarantees regularity in every characteristic. -/
theorem normalized_nullity_budget (B : Matrix ι ι K[X])
    (hzero : (evalRingHom (0 : K)).mapMatrix B = 1) (nodes : Finset K) :
    ∑ t ∈ nodes, (Fintype.card ι - ((evalRingHom t).mapMatrix B).rank) ≤ B.det.natDegree := by
  apply nullity_budget
  intro h
  have hd := congrArg Matrix.det hzero
  rw [← RingHom.map_det, h, map_zero, Matrix.det_one] at hd
  exact zero_ne_one hd

end DeterminantBudget
