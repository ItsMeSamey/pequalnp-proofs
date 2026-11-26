import ExactPlaneAffineSubstitution

namespace ExactPlaneTwoBitLookup

open ExactPlaneAffineSubstitution ExactPlaneSubsetPolynomial
open scoped BigOperators

def coefficients (a b c d : F) (S : Finset Bool) : F :=
  if false ∈ S then
    if true ∈ S then a+b+c+d else a+b
  else if true ∈ S then a+c else a

def bits (x y : F) : Finset Bool :=
  Finset.univ.filter fun j : Bool => (if j then y else x) = 1

private def entry (a b c d x y : F) : F :=
  if x=1 then (if y=1 then d else b) else (if y=1 then c else a)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem truth_table : ∀ a b c d x y : F,
    eval (coefficients a b c d) (bits x y) = entry a b c d x y := by decide

theorem eval_table (t : F × F → F) (x y : F) :
    eval (coefficients (t (0,0)) (t (1,0)) (t (0,1)) (t (1,1))) (bits x y) =
      t (x,y) := by
  rw [truth_table]
  have bit : ∀ z : F, z=0 ∨ z=1 := by decide
  rcases bit x with rfl | rfl <;> rcases bit y with rfl | rfl <;> simp [entry]

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem lookup_affine (table : F × F → F) (x y : Coeff I)
    (hx : degreeLE 1 x) (hy : degreeLE 1 y) :
    ∃ p : Coeff I, degreeLE 2 p ∧ ∀ A, eval p A = table (eval x A,eval y A) := by
  let c := coefficients (table (0,0)) (table (1,0)) (table (0,1)) (table (1,1))
  have dc : degreeLE 2 c := by
    intro S h
    have cap : S.card ≤ 2 := by simpa using Finset.card_le_univ S
    omega
  let rows : Bool → Coeff I := fun j => if j then y else x
  have aff : ∀ j, degreeLE 1 (rows j) := by
    intro j
    cases j <;> simp [rows,hx,hy]
  obtain ⟨p,dp,ev⟩ := affine_pullback c dc rows aff
  refine ⟨p,dp,fun A => ?_⟩
  have support : imageSupport rows A = bits (eval x A) (eval y A) := by
    ext j
    cases j <;> simp [imageSupport,rows,bits]
  rw [ev,support]
  exact eval_table table _ _

theorem lookup_sum {J : Type*} [Fintype J] (base : Coeff I) (hb : degreeLE 1 base)
    (table : J → F × F → F) (x y : J → Coeff I)
    (hx : ∀ j, degreeLE 1 (x j)) (hy : ∀ j, degreeLE 1 (y j)) :
    ∃ p : Coeff I, degreeLE 2 p ∧ ∀ A,
      eval p A = eval base A + ∑ j, table j (eval (x j) A, eval (y j) A) := by
  classical
  choose q dq eq using fun j => lookup_affine (table j) (x j) (y j) (hx j) (hy j)
  refine ⟨fun S => base S + ∑ j, q j S, ?_, ?_⟩
  · intro S h
    simp [hb S (by omega),fun j => dq j S h]
  · intro A
    simp only [eval,Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => eq j A)

#print axioms lookup_affine
#print axioms lookup_sum
end ExactPlaneTwoBitLookup
