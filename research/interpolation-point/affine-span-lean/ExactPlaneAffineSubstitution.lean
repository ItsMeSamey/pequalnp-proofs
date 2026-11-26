import ExactPlaneSubsetPolynomial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
namespace ExactPlaneAffineSubstitution
open ExactPlaneSubsetPolynomial
open scoped BigOperators
open Classical
abbrev F := ZMod 2
abbrev Coeff (I : Type*) := Finset I → F
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Boolean multiplication identifies x_i² with x_i. Coefficients of all
terms with the same union are added in F₂, including cancellations. -/
noncomputable def product (c e : Coeff I) (U : Finset I) : F :=
  ∑ S : Finset I, ∑ T : Finset I, if S∪T=U then c S*e T else 0

theorem product_degree (c e : Coeff I) {a b : Nat} (dc : degreeLE a c) (de : degreeLE b e) :
    degreeLE (a+b) (product c e) := by
  classical
  intro U hu
  apply Finset.sum_eq_zero
  intro S _
  apply Finset.sum_eq_zero
  intro T _
  by_cases eq : S∪T=U
  · rw [if_pos eq]
    have cap := Finset.card_union_le S T
    rw [eq] at cap
    by_cases big : a<S.card
    · simp [dc S big]
    · simp [de T (by omega)]
  · simp [eq]

private theorem test (c : Coeff I) (A : Finset I) :
    eval c A=∑ S : Finset I,if S⊆A then c S else 0 := by
  classical
  have filter : Finset.univ.filter (fun S : Finset I => S⊆A)=A.powerset := by ext; simp
  rw [←Finset.sum_filter,filter]
  rfl

theorem product_eval (c e : Coeff I) (A : Finset I) :
    eval (product c e) A=eval c A*eval e A := by
  classical
  unfold eval product
  rw [Finset.sum_comm]
  calc
    _ = ∑ S : Finset I,∑ T : Finset I,∑ U∈A.powerset,
          if S∪T=U then c S*e T else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.sum_comm]
    _ = ∑ S : Finset I,∑ T : Finset I,
          (if S⊆A then c S else 0)*(if T⊆A then e T else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro T _
      by_cases hs : S⊆A <;> by_cases ht : T⊆A <;> simp [Finset.union_subset_iff,hs,ht]
    _ = _ := by
      change _ = eval c A*eval e A
      rw [test c,test e,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum]

noncomputable def one (S : Finset I) : F := if S=∅ then 1 else 0
theorem one_degree : degreeLE 0 (one (I:=I)) := by
  intro S h
  have ne : S≠∅ := by rintro rfl; simp at h
  simp [one,ne]
theorem one_eval (A : Finset I) : eval (one (I:=I)) A=1 := by simp [one,eval]

/-- For each outer monomial, exhibit its squarefree expansion after
substitution. The proof grows its support bound by at most one per factor. -/
theorem monomial (rows : J→Coeff I) (aff : ∀ j,degreeLE 1 (rows j)) (S : Finset J) :
    ∃ f : Coeff I, degreeLE S.card f ∧ ∀ A,eval f A=∏ j∈S,eval (rows j) A := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨one,by simpa using (one_degree (I:=I)),fun A => by simp [one_eval]⟩
  | @insert j S hj ih =>
    obtain ⟨f,df,ef⟩ := ih
    refine ⟨product (rows j) f,?_,?_⟩
    · simpa [hj,Nat.add_comm] using product_degree (rows j) f (aff j) df
    · intro A; simp [product_eval,ef,hj]

/-- This preserves formal degree using union-product expansion, even for a
singular affine map, a constant coordinate, or an empty input alphabet. -/
theorem substitute (c : Coeff J) {d : Nat} (dc : degreeLE d c)
    (rows : J→Coeff I) (aff : ∀ j,degreeLE 1 (rows j)) :
    ∃ p : Coeff I, degreeLE d p ∧ ∀ A,
      eval p A=∑ S : Finset J,c S*∏ j∈S,eval (rows j) A := by
  classical
  choose term deg value using monomial rows aff
  let p := fun U => ∑ S : Finset J,c S*term S U
  refine ⟨p,?_,?_⟩
  · intro U hu
    apply Finset.sum_eq_zero
    intro S _
    by_cases hs : d<S.card
    · simp [dc S hs]
    · simp [deg S U (by omega)]
  · intro A
    change (∑ U∈A.powerset,∑ S : Finset J,c S*term S U)=_
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S _
    rw [←Finset.mul_sum]
    exact congrArg (fun z => c S*z) (value S A)

noncomputable def imageSupport (rows : J→Coeff I) (A : Finset I) : Finset J :=
  Finset.univ.filter (fun j => eval (rows j) A=1)

theorem affine_pullback (c : Coeff J) {d : Nat} (dc : degreeLE d c)
    (rows : J→Coeff I) (aff : ∀ j,degreeLE 1 (rows j)) :
    ∃ p : Coeff I,degreeLE d p ∧ ∀ A, eval p A=eval c (imageSupport rows A) := by
  classical
  obtain ⟨p,dp,correct⟩ := substitute c dc rows aff
  refine ⟨p,dp,?_⟩
  intro A
  rw [correct,test c (imageSupport rows A)]
  apply Finset.sum_congr rfl
  intro S _
  by_cases sub : S⊆imageSupport rows A
  · have all (j) (hj : j∈S) : eval (rows j) A=1 := (Finset.mem_filter.mp (sub hj)).2
    simp [if_pos sub,Finset.prod_eq_one all]
  · obtain ⟨j,hj,no⟩ := Finset.not_subset.mp sub
    have ne : eval (rows j) A≠1 := fun eq => no (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩)
    have bits : ∀ z : F, z=0 ∨ z=1 := by decide
    have zero := (bits _).resolve_right ne
    simp [if_neg sub,Finset.prod_eq_zero (f:=fun j => eval (rows j) A) hj zero]

/-- Actual affine constant and linear-coordinate weights. -/
noncomputable def affineRow (b : F) (w : I→F) (U : Finset I) : F :=
  (if U=∅ then b else 0) + ∑ i : I, if U={i} then w i else 0

theorem affineRow_degree (b : F) (w : I→F) : degreeLE 1 (affineRow b w) := by
  classical
  intro U large
  have empty : U≠∅ := by rintro rfl; simp at large
  have single (i : I) : U≠{i} := by rintro rfl; simp at large
  simp [affineRow,empty,single]

theorem affineRow_eval (b : F) (w : I→F) (A : Finset I) :
    eval (affineRow b w) A=b+∑ i∈A,w i := by
  classical
  unfold eval affineRow
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_powerset,Finset.empty_subset,ite_true,
    Finset.singleton_subset_iff]
  congr 1
  rw [←Finset.sum_filter]
  simp

theorem explicit_pullback (c : Coeff J) {d : Nat} (dc : degreeLE d c)
    (b : J→F) (w : J→I→F) :
    ∃ p : Coeff I,degreeLE d p ∧ ∀ A,eval p A=eval c
      (Finset.univ.filter (fun j => b j+(∑ i∈A,w j i)=1)) := by
  obtain ⟨p,h,eq⟩ := affine_pullback c dc (fun j => affineRow (b j) (w j)) (fun _ => affineRow_degree _ _)
  exact ⟨p,h,fun A => by simpa only [imageSupport,affineRow_eval] using eq A⟩
#print axioms affine_pullback
#print axioms explicit_pullback
end ExactPlaneAffineSubstitution
